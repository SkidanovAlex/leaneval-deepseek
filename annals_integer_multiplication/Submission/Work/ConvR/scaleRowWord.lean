import Mathlib
import Submission.Work.ConvR.scaleFacts
import Submission.Work.ConvR.extractScaleVec
import Submission.Work.ConvR.scaleRowCost

/-!
# ConvR: the row-scaling word (`Work.ConvR.scaleRowWord`)

`Work.ConvR.scaleRowWord` applies `FxLib.scale` (paper Lemma 2.2, scaling of one fixed-point
complex number by an integer `1 ≤ c ≤ 2^p`) coefficientwise to a whole vector
`u ∈ C̃◦^r` of fixed-point complex numbers, in cost `K (r+1) (p+1)^2 + K`.

The word is assembled from the `KernelLib` words:

* `KernelLib.mapList` runs the per-element word `q` on each coefficient of the list
  `u.map cfxVal` (the row `cvecVal u = ofList (u.map cfxVal)`), with the parameters
  `p, c` and the caller's `rest` staying below the list during the whole loop;
* `q` duplicates the two parameters on top of the element with two calls of
  `KernelLib.pick 2`

  `[x, p, c, rest]  -->  [c, x, p, c, rest]  -->  [p, c, x, p, c, rest]`

  and then runs `FxLib.scale`, which consumes the *copies* `p, c` and leaves
  `[w, p, c, rest]`;
* `scale` is exactly the fixed-point scaling of the element, so the per-element cost is
  `2 * (3 * Kp * (4 * p + 14)) + Ks (p+1)^2 = 6 Kp (4p+14) + Ks (p+1)^2`
  (the two `pick`s are cheap because all three values involved have encoding size `O(p)`).

The cost of `mapList` is `r * (c + Km (L + 1)) + Km` with `L = cfxSz p = 2p + 8`, which the
arithmetic lemma `Work.ConvR.scaleRowCost` contracts to `(84 Kp + Ks + 10 Km)(r+1)(p+1)^2`
plus the same constant.  The final extraction of the vector of results from the list of values
produced by `mapList` is `Work.ConvR.extractScaleVec`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.ConvR

open HvdH

local infixr:68 " ;;; " => HvdH.Cmd.seq

/-! ## `WordR` plumbing -/

/-- The consequence (monotonicity) rule for `WordR`, with the pre- and post-conditions
exposed as functions of the value stack. -/
theorem WordR_conseq' {main p : Cmd} {P P' : List Val → Prop} {Q Q' : List Val → List Val → Prop}
    {C C' : List Val → ℕ} (h : WordR main p P Q C) (hP : ∀ vs, P' vs → P vs)
    (hQ : ∀ vs out, P' vs → Q vs out → Q' vs out) (hC : ∀ vs, P' vs → C vs ≤ C' vs) :
    WordR main p P' Q' C' := by
  intro vs hP' s R hR
  obtain ⟨out, s', n, hQh, he, hn, hstk, hoth⟩ := h vs (hP vs hP') s R hR
  exact ⟨out, s', n, hQ vs out hP' hQh, he, le_trans hn (hC vs hP'), hstk, hoth⟩

/-- Sequential composition of two constant-cost `WordR`s whose intermediate value stack is
fixed (`out = B` for the first, `vs = B` for the second). -/
theorem WordR_seq_c' {main p q : Cmd} {A B : List Val} {R : List Val → Prop} {c1 c2 : ℕ}
    (h1 : WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c1))
    (h2 : WordR main q (fun vs => vs = B) (fun _ out => R out) (fun _ => c2)) :
    WordR main (.seq p q) (fun vs => vs = A) (fun _ out => R out) (fun _ => c1 + c2) := by
  intro vs hvs s T hT
  rw [hvs] at hT
  obtain ⟨mid, s₂, n₁, hQ, he₁, hn₁, hstk₁, hoth₁⟩ := h1 A rfl s T hT
  rw [hQ] at hstk₁
  obtain ⟨out, s₃, n₂, hQ', he₂, hn₂, hstk₂, hoth₂⟩ := h2 B rfl s₂ T hstk₁
  exact ⟨out, s₃, n₁ + n₂, hQ', Eval.seq he₁ he₂, Nat.add_le_add hn₁ hn₂, hstk₂,
    fun k hk => by rw [hoth₂ k hk, hoth₁ k hk]⟩

/-- `cfxVal` is injective. -/
theorem cfxVal_inj' {a b : ℤ × ℤ} (h : cfxVal a = cfxVal b) : a = b := by
  have h' : a.1 = b.1 ∧ a.2 = b.2 := by
    simpa [cfxVal, Val.cons.injEq, Val.int.injEq] using h
  exact Prod.ext h'.1 h'.2

/-! ## The per-element word

On `[x, p, c, rest]` with `x = cfxVal z`, `z` in the disc: copy `c` and then `p` to the top
(two `pick 2`) and run `scale`.  The output is `cfxVal w :: p :: c :: rest` with the scaling
error bound of paper Lemma 2.2. -/

theorem scaleElem {main : Cmd} {pickP : ℕ → Cmd} {scaleP : Cmd} {Kp Ks : ℕ}
    (hpick : ∀ (k : ℕ), WordR main (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs)
      (fun vs => Kp * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (hscale : ∀ (p c : ℕ), 1 ≤ c → c ≤ 2 ^ p → WordR main scaleP
      (fun vs => ∃ u rest, vs = .int (p : ℤ) :: .int (c : ℤ) :: cfxVal u :: rest ∧ inDisc p u)
      (fun vs out => ∃ u rest v, vs = .int (p : ℤ) :: .int (c : ℤ) :: cfxVal u :: rest ∧
        out = cfxVal v :: rest ∧ inDisc p v ∧
        ∀ x : ℂ, (c : ℝ) * ‖x‖ ≤ 1 →
          (2 : ℝ) ^ p * ‖fxC p v - (c : ℂ) * x‖ < 2 * c * ((2 : ℝ) ^ p * ‖fxC p u - x‖) + 3)
      (fun _ => Ks * (p + 1) ^ 2))
    (p c : ℕ) (hc1 : 1 ≤ c) (hc2 : c ≤ 2 ^ p) (rest₀ : List Val) (x : Val)
    (hx : ∃ z : ℤ × ℤ, x = cfxVal z ∧ inDisc p z) :
    WordR main (pickP 2 ;;; pickP 2 ;;; scaleP)
      (fun vs => vs = x :: .int (p : ℤ) :: .int (c : ℤ) :: rest₀)
      (fun _ out => ∃ y : Val, out = y :: .int (p : ℤ) :: .int (c : ℤ) :: rest₀ ∧
        (∃ z w : ℤ × ℤ, x = cfxVal z ∧ y = cfxVal w ∧ inDisc p w ∧
          ∀ x₀ : ℂ, (c : ℝ) * ‖x₀‖ ≤ 1 →
            (2 : ℝ) ^ p * ‖fxC p w - (c : ℂ) * x₀‖ < 2 * c * ((2 : ℝ) ^ p * ‖fxC p z - x₀‖) + 3) ∧
        vsz y ≤ cfxSz p)
      (fun _ => 6 * Kp * (4 * p + 14) + Ks * (p + 1) ^ 2) := by
  obtain ⟨z, rfl, hz⟩ := hx
  -- size bounds of the three values at the top of the stack
  have hb1 : vsz (cfxVal z) ≤ 2 * p + 8 := by
    simpa [cfxSz] using vsz_cfxVal_le hz
  have hb2 : isz (p : ℤ) ≤ p + 2 := by
    have h : p.size ≤ p := (Nat.size_le).mpr Nat.lt_two_pow_self
    simp only [isz, Int.natAbs_natCast]; omega
  have hb3 : isz (c : ℤ) ≤ p + 3 := by
    have h : (c : ℤ).natAbs ≤ 2 ^ p := by simpa using hc2
    exact isz_le_of_natAbs_le h
  -- the sums of the encoding sizes of the three values met by the two `pick 2`s
  have hs1 : (((cfxVal z :: .int (p : ℤ) :: .int (c : ℤ) :: rest₀).take 3).map vsz).sum ≤
      4 * p + 13 := by
    simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, vsz_int]
    omega
  have hs2 : (((.int (c : ℤ) :: cfxVal z :: .int (p : ℤ) :: .int (c : ℤ) :: rest₀).take 3).map vsz).sum ≤
      4 * p + 13 := by
    simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, vsz_int]
    omega
  -- step 1: copy `c` to the top
  have hstep1 : WordR main (pickP 2)
      (fun vs => vs = cfxVal z :: .int (p : ℤ) :: .int (c : ℤ) :: rest₀)
      (fun _ out => out = .int (c : ℤ) :: cfxVal z :: .int (p : ℤ) :: .int (c : ℤ) :: rest₀)
      (fun _ => 3 * Kp * (4 * p + 14)) := by
    refine WordR_conseq' (hpick 2) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]; simp
    · intro vs out hvs hout
      rw [hvs] at hout
      rw [hout]; simp
    · intro vs hvs
      rw [hvs]
      have h := hs1
      simp only [Nat.reduceAdd] at h ⊢
      nlinarith [h]
  -- step 2: copy `p` to the top
  have hstep2 : WordR main (pickP 2)
      (fun vs => vs = .int (c : ℤ) :: cfxVal z :: .int (p : ℤ) :: .int (c : ℤ) :: rest₀)
      (fun _ out => out = .int (p : ℤ) :: .int (c : ℤ) :: cfxVal z :: .int (p : ℤ) :: .int (c : ℤ) :: rest₀)
      (fun _ => 3 * Kp * (4 * p + 14)) := by
    refine WordR_conseq' (hpick 2) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]; simp
    · intro vs out hvs hout
      rw [hvs] at hout
      rw [hout]; simp
    · intro vs hvs
      rw [hvs]
      have h := hs2
      simp only [Nat.reduceAdd] at h ⊢
      nlinarith [h]
  -- step 3: scale the element by `c`
  have hstep3 : WordR main scaleP
      (fun vs => vs = .int (p : ℤ) :: .int (c : ℤ) :: cfxVal z :: .int (p : ℤ) :: .int (c : ℤ) :: rest₀)
      (fun _ out => ∃ w : ℤ × ℤ, out = cfxVal w :: .int (p : ℤ) :: .int (c : ℤ) :: rest₀ ∧
        inDisc p w ∧ ∀ x₀ : ℂ, (c : ℝ) * ‖x₀‖ ≤ 1 →
          (2 : ℝ) ^ p * ‖fxC p w - (c : ℂ) * x₀‖ <
            2 * c * ((2 : ℝ) ^ p * ‖fxC p z - x₀‖) + 3)
      (fun _ => Ks * (p + 1) ^ 2) := by
    refine WordR_conseq' (hscale p c hc1 hc2) ?_ ?_ ?_
    · intro vs hvs
      exact ⟨z, .int (p : ℤ) :: .int (c : ℤ) :: rest₀, hvs, hz⟩
    · intro vs out hvs hpost
      obtain ⟨u, r, v, heq, hout, hdisc, hbd⟩ := hpost
      have h1 : cfxVal z = cfxVal u ∧ r = .int (p : ℤ) :: .int (c : ℤ) :: rest₀ := by
        have h := hvs.symm.trans heq
        have h2 : cfxVal z = cfxVal u ∧ .int (p : ℤ) :: .int (c : ℤ) :: rest₀ = r := by
          simpa [List.cons.injEq] using h
        exact ⟨h2.1, h2.2.symm⟩
      have huz : u = z := cfxVal_inj' h1.1.symm
      subst huz
      exact ⟨v, by rw [hout, h1.2], hdisc, hbd⟩
    · intro vs hvs
      exact le_rfl
  -- assemble, and collapse the two `3 * Kp * (4 * p + 14)` into `6 * Kp * (4 * p + 14)`
  refine WordR_conseq' (WordR_seq_c' hstep1 (WordR_seq_c' hstep2 hstep3)) ?_ ?_ ?_
  · intro vs hvs
    exact hvs
  · intro vs out hvs hq
    obtain ⟨w, hout, hdisc, hbd⟩ := hq
    exact ⟨cfxVal w, hout, ⟨z, w, rfl, rfl, hdisc, hbd⟩,
      by simpa [cfxSz] using vsz_cfxVal_le hdisc⟩
  · intro vs hvs
    have h1 : 3 * Kp * (4 * p + 14) + (3 * Kp * (4 * p + 14) + Ks * (p + 1) ^ 2) ≤
        6 * Kp * (4 * p + 14) + Ks * (p + 1) ^ 2 := by nlinarith
    exact h1

/-! ## The row-scaling word -/

theorem scaleRowWord (hK : HvdH.KernelLib) (hF : HvdH.FxLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p c r : ℕ), 1 ≤ c → c ≤ 2 ^ p →
      ∀ (u : List (ℤ × ℤ)) (rest : List HvdH.Val), HvdH.InDiscVec p r u →
        HvdH.WordR main prog
          (fun vs => vs = HvdH.cvecVal u :: HvdH.Val.int (p : ℤ) :: HvdH.Val.int (c : ℤ) :: rest)
          (fun _ out => ∃ v : List (ℤ × ℤ),
            out = HvdH.cvecVal v :: HvdH.Val.int (p : ℤ) :: HvdH.Val.int (c : ℤ) :: rest ∧
            HvdH.InDiscVec p r v ∧
            ∀ (j : Fin r) (x : ℂ), (c : ℝ) * ‖x‖ ≤ 1 →
              (2 : ℝ) ^ p * ‖HvdH.fxC p (v.getD j (0, 0)) - (c : ℂ) * x‖ <
                2 * c * ((2 : ℝ) ^ p * ‖HvdH.fxC p (u.getD j (0, 0)) - x‖) + 3)
          (fun _ => K * (r + 1) * (p + 1) ^ 2 + K) := by
  obtain ⟨pickP, Kp, hpick⟩ := hK.pick
  obtain ⟨mapP, Km, hmap⟩ := hK.mapList
  obtain ⟨scaleP, Ks, hscale⟩ := hF.scale
  refine ⟨mapP (pickP 2 ;;; pickP 2 ;;; scaleP), 84 * Kp + Ks + 10 * Km, ?_⟩
  intro main p c r hc1 hc2 u rest hu
  -- the encoding size of every element of the row is bounded by `cfxSz p`
  have hxs : ∀ x ∈ u.map cfxVal,
      (∃ z : ℤ × ℤ, x = cfxVal z ∧ inDisc p z) ∧ vsz x ≤ cfxSz p := by
    intro x hx
    obtain ⟨z, hzu, hzx⟩ := List.mem_map.mp hx
    rw [← hzx]
    exact ⟨⟨z, rfl, hu.2 z hzu⟩, by simpa [cfxSz] using vsz_cfxVal_le (hu.2 z hzu)⟩
  have hmain := hmap main (pickP 2 ;;; pickP 2 ;;; scaleP) (.int (p : ℤ) :: .int (c : ℤ) :: rest)
      (fun x => ∃ z : ℤ × ℤ, x = cfxVal z ∧ inDisc p z)
      (fun x y => ∃ z w : ℤ × ℤ, x = cfxVal z ∧ y = cfxVal w ∧ inDisc p w ∧
        ∀ x₀ : ℂ, (c : ℝ) * ‖x₀‖ ≤ 1 →
          (2 : ℝ) ^ p * ‖fxC p w - (c : ℂ) * x₀‖ <
            2 * c * ((2 : ℝ) ^ p * ‖fxC p z - x₀‖) + 3)
      (6 * Kp * (4 * p + 14) + Ks * (p + 1) ^ 2) (cfxSz p)
      (fun x hx => scaleElem (hpick main) (hscale main) p c hc1 hc2 rest x hx) (u.map cfxVal) hxs
  refine WordR_conseq' hmain ?_ ?_ ?_
  · intro vs hvs
    exact hvs
  · intro vs out hvs hq
    obtain ⟨ys, hout, hF2⟩ := hq
    obtain ⟨v, hofList, hv, hbd⟩ := extractScaleVec hu hF2
    exact ⟨v, by rw [hout, hofList], hv, hbd⟩
  · intro vs hvs
    have hlen : (u.map cfxVal).length = r := by rw [List.length_map, hu.1]
    rw [hlen]
    exact scaleRowCost Kp Km Ks r p

end Work.ConvR
