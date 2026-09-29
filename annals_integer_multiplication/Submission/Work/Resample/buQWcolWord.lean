import Mathlib
import Submission.Work.Resample.buQWstepKit
import Submission.Work.Resample.buQWprodElem
import Submission.Work.Resample.buQWelemWord
import Submission.Work.Resample.buQWr1Rot
import Submission.Work.Resample.buZipWithFun

/-!
# `Work.Resample.buQWcolWord`: one column step of the truncated Neumann round

The word reads the pair `(h, w)` (a shift and the column of tabulated weights for that shift)
together with the current accumulator `z` and the frame `(σ, v, acc, s, p)`, and returns
`buAddV z (buMulCol w (buRot ((h % s).toNat) v))`, i.e. it adds the shifted, weighted vector to the
accumulator while leaving the frame untouched.  It is the body of the fold over `buColsT` in the
round word `Work.Resample.buQWstep`.

The program is the chain

`unconsV ;;; pick 6 ;;; swap ;;; fmod ;;; pick 4 ;;; swap ;;;` (rotate) `;;; swap` (product)
`;;; swap` (sum),

and it works because the `s` used for the reduction of `h` was *copied* (not moved), so that the
copy needed in the final frame already sits directly below the accumulator.

The three pieces are proved here as `buQWcmMul` (pointwise product, via
`Work.Resample.buQWprodElem` and `KernelLib.zipWith`), `buQWcmAdd` (pointwise sum, via
`Work.Resample.buQWelemAdd`) and the rotation word `Work.Resample.buQWr1Rot`.
-/

set_option autoImplicit false
set_option maxHeartbeats 50000000
set_option maxRecDepth 8000

namespace Work.Resample

open HvdH

/-! ## 1.  helpers -/

/-- A `WordR` with the explicit `∃ r` window form gives, for each concrete tail, the `WordR` with a
fixed window. -/
theorem buQWcm_ofWordR {main prog : Cmd} {A B : List Val} {c : ℕ}
    (h : WordR main prog (fun vs => ∃ r, vs = A ++ r)
      (fun vs out => ∃ r, vs = A ++ r ∧ out = B ++ r) (fun _ => c)) (rest : List Val) :
    WordR main prog (fun vs => vs = A ++ rest) (fun _ out => out = B ++ rest) (fun _ => c) := by
  intro vs hvs s R hR
  obtain ⟨out, s', n, ⟨r, hvs', hout⟩, hev, hn, hstk, hoth⟩ := h vs ⟨rest, hvs⟩ s R hR
  have hr : r = rest := List.append_cancel_left (hvs'.symm.trans hvs)
  exact ⟨out, s', n, by rw [hout, hr], hev, hn, hstk, hoth⟩

/-- `isz` of a product. -/
theorem buQWcol_isz_mul_le (a b : ℤ) : isz (a * b) ≤ isz a + isz b := by
  have h1 : (a * b).natAbs = a.natAbs * b.natAbs := Int.natAbs_mul a b
  have h2 : (a.natAbs * b.natAbs).size ≤ a.natAbs.size + b.natAbs.size := size_mul_le _ _
  simp only [isz, h1]
  omega

/-- `isz` of a sum. -/
theorem buQWcol_isz_add_le (a b : ℤ) : isz (a + b) ≤ max (isz a) (isz b) + 1 := by
  set A : ℕ := max a.natAbs.size b.natAbs.size with hA
  have ha : a.natAbs < 2 ^ A := by
    rw [hA]
    exact lt_of_lt_of_le (Nat.size_le.mp (le_refl a.natAbs.size))
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_max_left _ _))
  have hb : b.natAbs < 2 ^ A := by
    rw [hA]
    exact lt_of_lt_of_le (Nat.size_le.mp (le_refl b.natAbs.size))
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_max_right _ _))
  have h2 : (a + b).natAbs < 2 ^ (A + 1) := by
    calc (a + b).natAbs ≤ a.natAbs + b.natAbs := Int.natAbs_add_le a b
      _ < 2 ^ A + 2 ^ A := add_lt_add ha hb
      _ = 2 ^ (A + 1) := by rw [pow_succ]; ring
  have h3 : (a + b).natAbs.size ≤ A + 1 := Nat.size_le.mpr h2
  have h4 : A + 2 ≤ max (isz a) (isz b) := by
    rw [hA]
    simp only [isz]
    omega
  simp only [isz]
  omega

/-- `getD` of a mapped list of integers. -/
theorem buQWcm_getD_map_int {l : List ℤ} {i : ℕ} (hi : i < l.length) :
    (l.map Val.int).getD i .nil = Val.int (l.getD i 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    ← List.getD_eq_getElem _ _ hi]

/-- `getD` of a mapped list of complex pairs. -/
theorem buQWcm_getD_map_cfx {l : List (ℤ × ℤ)} {i : ℕ} (hi : i < l.length) :
    (l.map cfxVal).getD i .nil = cfxVal (l.getD i (0, 0)) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    ← List.getD_eq_getElem _ _ hi]

/-- `isz` of a product of a small weight and a small coordinate. -/
theorem buQWcol_isz_mul_small {p : ℕ} {a b : ℤ} (ha : isz a ≤ p + 3) (hb : isz b ≤ p + 5) :
    isz (a * b) ≤ 2 * p + 8 := by
  have h := buQWcol_isz_mul_le a b
  omega

/-- `isz` of a sum of two bounded coordinates. -/
theorem buQWcol_isz_add_small {p : ℕ} {a b : ℤ} (ha : isz a ≤ 2 * p + 8) (hb : isz b ≤ 2 * p + 8) :
    isz (a + b) ≤ 2 * p + 9 := by
  have h := buQWcol_isz_add_le a b
  omega

/-- Membership in a `zip`. -/
theorem buQWcm_mem_zip {α β : Type} {l₁ : List α} {l₂ : List β} {x : α} {y : β}
    (h : (x, y) ∈ l₁.zip l₂) : x ∈ l₁ ∧ y ∈ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp at h
  | cons a as ih =>
      cases l₂ with
      | nil => simp at h
      | cons b bs =>
          simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩ | h
          · exact ⟨by simp, by simp⟩
          · obtain ⟨h1, h2⟩ := ih h
            exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

/-- `K * A ≤ KS * (10^6 * E)` when `K ≤ KS` and `A ≤ 10^5 * E`. -/
theorem buQWcol_cheapLe {K KS A E : ℕ} (hKS : K ≤ KS) (hA : A ≤ 100000 * E) :
    K * A ≤ KS * (1000000 * E) := by
  calc K * A ≤ KS * A := Nat.mul_le_mul_right A hKS
    _ ≤ KS * (100000 * E) := Nat.mul_le_mul_left KS hA
    _ ≤ KS * (1000000 * E) := Nat.mul_le_mul_left KS (Nat.mul_le_mul_right E (by norm_num))

/-- The cost arithmetic of `Work.Resample.buQWcolWord`: ten cheap window steps of cost at most
`KS * 10^6 * (s+1) * (p+1)` and one product step of cost `Kmul * (s+1) * (CmKmul + p + 1)` fit
into `Kc * (s+1) * (CmKc + p + 1)` for `Kc = Kmul + 10^7 * KS + 1000`. -/
theorem buQWcol_cost {Kmul Kc KS s p CmKmul CmKc c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : ℕ}
    (h1 : c1 ≤ KS * (1000000 * ((s + 1) * (p + 1))))
    (h2 : c2 ≤ KS * (1000000 * ((s + 1) * (p + 1))))
    (h3 : c3 ≤ KS * (1000000 * ((s + 1) * (p + 1))))
    (h4 : c4 ≤ KS * (1000000 * ((s + 1) * (p + 1))))
    (h5 : c5 ≤ KS * (1000000 * ((s + 1) * (p + 1))))
    (h6 : c6 ≤ KS * (1000000 * ((s + 1) * (p + 1))))
    (h7 : c7 ≤ KS * (1000000 * ((s + 1) * (p + 1))))
    (h8 : c8 ≤ KS * (1000000 * ((s + 1) * (p + 1))))
    (h9 : c9 ≤ Kmul * (s + 1) * (CmKmul + p + 1))
    (h10 : c10 ≤ KS * (1000000 * ((s + 1) * (p + 1))))
    (h11 : c11 ≤ KS * (1000000 * ((s + 1) * (p + 1))))
    (hCm : CmKmul ≤ CmKc)
    (hKc : Kc = Kmul + 10000000 * KS + 1000) :
    c1 + (c2 + (c3 + (c4 + (c5 + (c6 + (c7 + (c8 + (c9 + (c10 + c11)))))))))
      ≤ Kc * (s + 1) * (CmKc + p + 1) := by
  have hcheap : c1 + (c2 + (c3 + (c4 + (c5 + (c6 + (c7 + (c8 + (c10 + c11))))))))
      ≤ (10 * KS) * (1000000 * ((s + 1) * (p + 1))) := by
    linarith [h1, h2, h3, h4, h5, h6, h7, h8, h10, h11]
  have htotal : c1 + (c2 + (c3 + (c4 + (c5 + (c6 + (c7 + (c8 + (c9 + (c10 + c11)))))))))
      ≤ (10 * KS) * (1000000 * ((s + 1) * (p + 1))) + Kmul * (s + 1) * (CmKmul + p + 1) := by
    linarith [hcheap, h9]
  have hstep : (10 * KS) * (1000000 * ((s + 1) * (p + 1))) + Kmul * (s + 1) * (CmKmul + p + 1)
      ≤ Kc * (s + 1) * (CmKc + p + 1) := by
    rw [hKc]
    have hE : (s + 1) * (p + 1) ≤ (s + 1) * (CmKc + p + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hm1 : (10 * KS) * (1000000 * ((s + 1) * (p + 1)))
        ≤ (10000000 * KS) * ((s + 1) * (CmKc + p + 1)) := by
      calc (10 * KS) * (1000000 * ((s + 1) * (p + 1)))
          = (10000000 * KS) * ((s + 1) * (p + 1)) := by ring
        _ ≤ (10000000 * KS) * ((s + 1) * (CmKc + p + 1)) := Nat.mul_le_mul_left _ hE
    have hm2 : Kmul * (s + 1) * (CmKmul + p + 1) ≤ Kmul * ((s + 1) * (CmKc + p + 1)) := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left Kmul (Nat.mul_le_mul_left _ (by omega))
    calc (10 * KS) * (1000000 * ((s + 1) * (p + 1))) + Kmul * (s + 1) * (CmKmul + p + 1)
        ≤ (10000000 * KS) * ((s + 1) * (CmKc + p + 1)) + Kmul * ((s + 1) * (CmKc + p + 1)) :=
          add_le_add hm1 hm2
      _ = (10000000 * KS + Kmul) * ((s + 1) * (CmKc + p + 1)) := by ring
      _ ≤ (Kmul + 10000000 * KS + 1000) * ((s + 1) * (CmKc + p + 1)) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = (Kmul + 10000000 * KS + 1000) * (s + 1) * (CmKc + p + 1) := by ring
  linarith [htotal, hstep]

/-! ## 2.  the pointwise product word -/

/-- The element map of the pointwise product. -/
def buQWcmF : Val → Val → Val
  | .int c, .cons (.int a) (.int b) => .cons (.int (c * a)) (.int (c * b))
  | _, _ => .nil

theorem buQWcmF_cfxVal (c : ℤ) (z : ℤ × ℤ) :
    buQWcmF (Val.int c) (cfxVal z) = cfxVal (c * z.1, c * z.2) := rfl

/-- The `zipWith` of `buQWcmF` over the two encoded lists is the encoding of `buMulCol`. -/
theorem buQWcm_zip_eq (w : List ℤ) : ∀ v : List (ℤ × ℤ),
    List.zipWith buQWcmF (w.map Val.int) (v.map cfxVal) = (buMulCol w v).map cfxVal := by
  induction w with
  | nil => intro v; cases v <;> rfl
  | cons c ws ih =>
      intro v
      cases v with
      | nil => rfl
      | cons z vs =>
          change cfxVal (c * z.1, c * z.2)
              :: List.zipWith buQWcmF (ws.map Val.int) (vs.map cfxVal)
            = cfxVal (c * z.1, c * z.2)
              :: ((ws.zip vs).map (fun a : ℤ × (ℤ × ℤ) =>
                  (a.1 * a.2.1, a.1 * a.2.2))).map cfxVal
          simp only [ih vs, buMulCol]

theorem buQWcmMul (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (q : HvdH.Cmd) (Kc : ℕ),
    ∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ) (p : ℕ) (w : List ℤ) (v : List (ℤ × ℤ)),
      Monotone Cm → HvdH.MulBelow main N Cm → 100 ≤ p → Kc * p < N →
      w.length = v.length → (∀ y ∈ w, HvdH.isz y ≤ p + 3) →
      (∀ y ∈ v, HvdH.isz y.1 ≤ p + 5 ∧ HvdH.isz y.2 ≤ p + 5) →
      Work.Resample.Pipe main q [HvdH.ofList (w.map HvdH.Val.int), HvdH.cvecVal v]
        [HvdH.cvecVal (Work.Resample.buMulCol w v)]
        (Kc * (w.length + 1) * (Cm (Kc * p) + p + 1)) := by
  obtain ⟨comb, Kz, hzip⟩ := buZipWithFun KL
  obtain ⟨qpe, Kpe, hpe⟩ := buQWprodElem KL IL
  refine ⟨comb qpe, 1000 * (Kpe + Kz + 1), ?_⟩
  intro main N Cm p w v hmono hmb hp hKN hlen hwisz hvsz
  have hKpe_le : Kpe ≤ 1000 * (Kpe + Kz + 1) := by omega
  have hKN' : Kpe * p < N := lt_of_le_of_lt (Nat.mul_le_mul_right p hKpe_le) hKN
  have hcmB : Cm (Kpe * p) ≤ Cm ((1000 * (Kpe + Kz + 1)) * p) :=
    hmono (Nat.mul_le_mul_right p hKpe_le)
  intro rest
  set P : Val → Val → Prop := fun x y => ∃ (c : ℤ) (z : ℤ × ℤ), x = Val.int c ∧ y = cfxVal z ∧
    isz c ≤ p + 3 ∧ z.1.natAbs.size ≤ p + 3 ∧ z.2.natAbs.size ≤ p + 3 with hP
  have hbody : ∀ x y, P x y → WordR main qpe (fun vs => vs = x :: y :: rest)
      (fun _ out => out = buQWcmF x y :: rest) (fun _ => Kpe * (Cm (Kpe * p) + p + 1)) := by
    intro x y hxy
    obtain ⟨c, z, rfl, rfl, hc, hz1, hz2⟩ := hxy
    intro vs hvs s R hR
    have hv2 : vs = Val.int c :: cfxVal z :: rest := hvs
    obtain ⟨out, s', n, hpost, hev, hn, hstk, hoth⟩ :=
      hpe main N Cm p c z hmono hmb hp hKN' hc hz1 hz2 rest vs hv2 s R hR
    refine ⟨out, s', n, ?_, hev, hn, hstk, hoth⟩
    simpa only [buQWcmF_cfxVal, List.cons_append, List.nil_append] using hpost
  have hlenmap : (w.map Val.int).length = (v.map cfxVal).length := by
    simp only [List.length_map, hlen]
  have hPmem : ∀ i < (w.map Val.int).length,
      P ((w.map Val.int).getD i .nil) ((v.map cfxVal).getD i .nil) := by
    intro i hi
    rw [List.length_map] at hi
    have hiv : i < v.length := by rw [← hlen]; exact hi
    refine ⟨w.getD i 0, v.getD i (0, 0), buQWcm_getD_map_int hi, buQWcm_getD_map_cfx hiv,
      ?_, ?_, ?_⟩
    · exact hwisz _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _)
    · have h1 := (hvsz (v.getD i (0, 0))
          (by rw [List.getD_eq_getElem _ _ hiv]; exact List.getElem_mem _)).1
      simp only [isz] at h1
      omega
    · have h1 := (hvsz (v.getD i (0, 0))
          (by rw [List.getD_eq_getElem _ _ hiv]; exact List.getElem_mem _)).2
      simp only [isz] at h1
      omega
  have hLmem : ∀ x ∈ (w.map Val.int) ++ (v.map cfxVal), vsz x ≤ 4 * p + 20 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      rw [Work.Fx.vsz_int]
      have h1 := hwisz c hc
      omega
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      rw [Work.Fx.vsz_cfxVal]
      have h1 := (hvsz z hz).1
      have h2 := (hvsz z hz).2
      omega
  have hLfun : ∀ x y, P x y → vsz (buQWcmF x y) ≤ 4 * p + 20 := by
    intro x y hxy
    obtain ⟨c, z, rfl, rfl, hc, hz1, hz2⟩ := hxy
    rw [buQWcmF_cfxVal c z, Work.Fx.vsz_cfxVal]
    change isz (c * z.1) + isz (c * z.2) + 1 ≤ 4 * p + 20
    have h2 : isz z.1 ≤ p + 5 := by simp only [isz] at hz1 ⊢; omega
    have h3 : isz z.2 ≤ p + 5 := by simp only [isz] at hz2 ⊢; omega
    have hm1 := buQWcol_isz_mul_le c z.1
    have hm2 := buQWcol_isz_mul_le c z.2
    omega
  have hzw := hzip main qpe rest P buQWcmF (Kpe * (Cm (Kpe * p) + p + 1)) (4 * p + 20)
    hbody hLfun (w.map Val.int) (v.map cfxVal) hlenmap hPmem hLmem
  rw [buQWcm_zip_eq w v] at hzw
  have hcost : (w.map Val.int).length
        * (Kpe * (Cm (Kpe * p) + p + 1) + Kz * (4 * p + 20 + 1)) + Kz
      ≤ (1000 * (Kpe + Kz + 1)) * (w.length + 1)
        * (Cm ((1000 * (Kpe + Kz + 1)) * p) + p + 1) := by
    rw [List.length_map]
    set K : ℕ := 1000 * (Kpe + Kz + 1) with hK
    set X : ℕ := Cm (K * p) + p + 1 with hX
    have hmain1 : Kpe * (Cm (Kpe * p) + p + 1) ≤ (500 * (Kpe + Kz + 1)) * X := by
      have hle : (Cm (Kpe * p) + p + 1) ≤ X := by rw [hX]; omega
      calc Kpe * (Cm (Kpe * p) + p + 1) ≤ (500 * (Kpe + Kz + 1)) * (Cm (Kpe * p) + p + 1) :=
            Nat.mul_le_mul_right _ (by omega)
        _ ≤ (500 * (Kpe + Kz + 1)) * X := Nat.mul_le_mul_left _ hle
    have hmain2 : Kz * (4 * p + 20 + 1) ≤ (500 * (Kpe + Kz + 1)) * X := by
      have h1 : 4 * p + 20 + 1 ≤ 6 * (p + 1) := by omega
      calc Kz * (4 * p + 20 + 1) ≤ Kz * (6 * (p + 1)) := Nat.mul_le_mul_left _ h1
        _ = (6 * Kz) * (p + 1) := by ring
        _ ≤ (500 * (Kpe + Kz + 1)) * (p + 1) := Nat.mul_le_mul_right _ (by omega)
        _ ≤ (500 * (Kpe + Kz + 1)) * X := Nat.mul_le_mul_left _ (by rw [hX]; omega)
    have hbr : Kpe * (Cm (Kpe * p) + p + 1) + Kz * (4 * p + 20 + 1) ≤ K * X := by
      have hs := add_le_add hmain1 hmain2
      calc Kpe * (Cm (Kpe * p) + p + 1) + Kz * (4 * p + 20 + 1)
          ≤ (500 * (Kpe + Kz + 1)) * X + (500 * (Kpe + Kz + 1)) * X := hs
        _ = K * X := by rw [hK]; ring
    have hKz : Kz ≤ K * X := by
      have h1 : Kz ≤ K := by rw [hK]; omega
      calc Kz ≤ K := h1
        _ = K * 1 := (Nat.mul_one K).symm
        _ ≤ K * X := Nat.mul_le_mul_left K (by rw [hX]; omega)
    calc w.length * (Kpe * (Cm (Kpe * p) + p + 1) + Kz * (4 * p + 20 + 1)) + Kz
        ≤ w.length * (K * X) + K * X := Nat.add_le_add (Nat.mul_le_mul_left _ hbr) hKz
      _ = K * (w.length + 1) * X := by ring
      _ = (1000 * (Kpe + Kz + 1)) * (w.length + 1)
          * (Cm ((1000 * (Kpe + Kz + 1)) * p) + p + 1) := by rw [hK, hX]
  refine KL.conseq main (comb qpe)
    (fun vs => vs = ofList (w.map Val.int) :: ofList (v.map cfxVal) :: rest)
    (fun vs => vs = [ofList (w.map Val.int), cvecVal v] ++ rest)
    (fun _ out => out = ofList ((buMulCol w v).map cfxVal) :: rest)
    (fun _ out => out = [cvecVal (buMulCol w v)] ++ rest)
    (fun _ => (w.map Val.int).length
      * (Kpe * (Cm (Kpe * p) + p + 1) + Kz * (4 * p + 20 + 1)) + Kz)
    (fun _ => 1000 * (Kpe + Kz + 1) * (w.length + 1)
      * (Cm (1000 * (Kpe + Kz + 1) * p) + p + 1))
    hzw ?_ ?_ ?_
  · intro vs h
    rw [h]
    rfl
  · intro vs out _ hq
    rw [hq]
    rfl
  · intro vs _
    exact hcost

/-! ## 3.  the pointwise sum word -/

/-- The element map of the pointwise sum. -/
def buQWcaF : Val → Val → Val
  | .cons (.int a1) (.int a2), .cons (.int b1) (.int b2) =>
      .cons (.int (a1 + b1)) (.int (a2 + b2))
  | _, _ => .nil

theorem buQWcaF_cfxVal (u v : ℤ × ℤ) :
    buQWcaF (cfxVal u) (cfxVal v) = cfxVal (u.1 + v.1, u.2 + v.2) := rfl

/-- The `zipWith` of `buQWcaF` over two encoded vectors is the encoding of `buAddV`. -/
theorem buQWca_zip_eq (a : List (ℤ × ℤ)) : ∀ b : List (ℤ × ℤ),
    List.zipWith buQWcaF (a.map cfxVal) (b.map cfxVal) = (buAddV a b).map cfxVal := by
  induction a with
  | nil => intro b; cases b <;> rfl
  | cons u as ih =>
      intro b
      cases b with
      | nil => rfl
      | cons v bs =>
          change cfxVal (u.1 + v.1, u.2 + v.2)
              :: List.zipWith buQWcaF (as.map cfxVal) (bs.map cfxVal)
            = cfxVal (u.1 + v.1, u.2 + v.2) :: (buAddV as bs).map cfxVal
          simp only [ih bs]

theorem buQWcmAdd (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (q : HvdH.Cmd) (Kc : ℕ),
    ∀ (main : HvdH.Cmd) (P : ℕ) (a b : List (ℤ × ℤ)),
      a.length = b.length →
      (∀ z ∈ a, HvdH.isz z.1 ≤ P ∧ HvdH.isz z.2 ≤ P) →
      (∀ z ∈ b, HvdH.isz z.1 ≤ P ∧ HvdH.isz z.2 ≤ P) →
      Work.Resample.Pipe main q [HvdH.cvecVal a, HvdH.cvecVal b]
        [HvdH.cvecVal (Work.Resample.buAddV a b)] (Kc * (a.length + 1) * (P + 1)) := by
  obtain ⟨comb, Kz, hzip⟩ := buZipWithFun KL
  obtain ⟨qel, Ke, hel⟩ := buQWelemAdd KL IL
  refine ⟨comb qel, 100 * (Ke + Kz + 1), ?_⟩
  intro main P a b hlen ha hb
  intro rest
  set PP : Val → Val → Prop := fun x y => ∃ u v : ℤ × ℤ, x = cfxVal u ∧ y = cfxVal v ∧
    isz u.1 ≤ P ∧ isz u.2 ≤ P ∧ isz v.1 ≤ P ∧ isz v.2 ≤ P with hPP
  have hbody : ∀ x y, PP x y → WordR main qel (fun vs => vs = x :: y :: rest)
      (fun _ out => out = buQWcaF x y :: rest) (fun _ => Ke * (P + 1)) := by
    intro x y hxy
    obtain ⟨u, v, rfl, rfl, hu1, hu2, hv1, hv2⟩ := hxy
    have h := buQWcm_ofWordR (A := [cfxVal u, cfxVal v])
      (B := [cfxVal (u.1 + v.1, u.2 + v.2)]) (hel main P u v hu1 hu2 hv1 hv2) rest
    intro vs hvs s R hR
    obtain ⟨out, s', n, hpost, hev, hn, hstk, hoth⟩ := h vs hvs s R hR
    refine ⟨out, s', n, ?_, hev, hn, hstk, hoth⟩
    simpa only [buQWcaF_cfxVal, List.cons_append, List.nil_append] using hpost
  have hlenmap : (a.map cfxVal).length = (b.map cfxVal).length := by
    simp only [List.length_map, hlen]
  have hPmem : ∀ i < (a.map cfxVal).length,
      PP ((a.map cfxVal).getD i .nil) ((b.map cfxVal).getD i .nil) := by
    intro i hi
    rw [List.length_map] at hi
    have hib : i < b.length := by rw [← hlen]; exact hi
    refine ⟨a.getD i (0, 0), b.getD i (0, 0), buQWcm_getD_map_cfx hi, buQWcm_getD_map_cfx hib,
      ?_, ?_, ?_, ?_⟩
    · exact (ha (a.getD i (0, 0))
        (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _)).1
    · exact (ha (a.getD i (0, 0))
        (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _)).2
    · exact (hb (b.getD i (0, 0))
        (by rw [List.getD_eq_getElem _ _ hib]; exact List.getElem_mem _)).1
    · exact (hb (b.getD i (0, 0))
        (by rw [List.getD_eq_getElem _ _ hib]; exact List.getElem_mem _)).2
  have hLmem : ∀ x ∈ (a.map cfxVal) ++ (b.map cfxVal), vsz x ≤ 2 * P + 4 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      rw [Work.Fx.vsz_cfxVal]
      have h1 := (ha z hz).1
      have h2 := (ha z hz).2
      omega
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      rw [Work.Fx.vsz_cfxVal]
      have h1 := (hb z hz).1
      have h2 := (hb z hz).2
      omega
  have hLfun : ∀ x y, PP x y → vsz (buQWcaF x y) ≤ 2 * P + 4 := by
    intro x y hxy
    obtain ⟨u, v, rfl, rfl, hu1, hu2, hv1, hv2⟩ := hxy
    rw [buQWcaF_cfxVal u v, Work.Fx.vsz_cfxVal]
    change isz (u.1 + v.1) + isz (u.2 + v.2) + 1 ≤ 2 * P + 4
    have h1 : isz (u.1 + v.1) ≤ P + 1 := by
      have := buQWcol_isz_add_le u.1 v.1
      omega
    have h2 : isz (u.2 + v.2) ≤ P + 1 := by
      have := buQWcol_isz_add_le u.2 v.2
      omega
    omega
  have hzw := hzip main qel rest PP buQWcaF (Ke * (P + 1)) (2 * P + 4) hbody hLfun
    (a.map cfxVal) (b.map cfxVal) hlenmap hPmem hLmem
  rw [buQWca_zip_eq a b] at hzw
  have hcost : (a.map cfxVal).length * (Ke * (P + 1) + Kz * (2 * P + 4 + 1)) + Kz
      ≤ (100 * (Ke + Kz + 1)) * (a.length + 1) * (P + 1) := by
    rw [List.length_map]
    set K : ℕ := 100 * (Ke + Kz + 1) with hK
    have hbr : Ke * (P + 1) + Kz * (2 * P + 4 + 1) ≤ K * (P + 1) := by
      have h1 : Ke * (P + 1) ≤ (50 * (Ke + Kz + 1)) * (P + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 : Kz * (2 * P + 4 + 1) ≤ (50 * (Ke + Kz + 1)) * (P + 1) := by
        have h3 : 2 * P + 4 + 1 ≤ 6 * (P + 1) := by omega
        calc Kz * (2 * P + 4 + 1) ≤ Kz * (6 * (P + 1)) := Nat.mul_le_mul_left _ h3
          _ = (6 * Kz) * (P + 1) := by ring
          _ ≤ (50 * (Ke + Kz + 1)) * (P + 1) := Nat.mul_le_mul_right _ (by omega)
      have hs := add_le_add h1 h2
      calc Ke * (P + 1) + Kz * (2 * P + 4 + 1)
          ≤ (50 * (Ke + Kz + 1)) * (P + 1) + (50 * (Ke + Kz + 1)) * (P + 1) := hs
        _ = K * (P + 1) := by rw [hK]; ring
    have hKz : Kz ≤ K * (P + 1) := by
      have h1 : Kz ≤ K := by rw [hK]; omega
      calc Kz ≤ K := h1
        _ = K * 1 := (Nat.mul_one K).symm
        _ ≤ K * (P + 1) := Nat.mul_le_mul_left K (by omega)
    calc a.length * (Ke * (P + 1) + Kz * (2 * P + 4 + 1)) + Kz
        ≤ a.length * (K * (P + 1)) + K * (P + 1) := Nat.add_le_add (Nat.mul_le_mul_left _ hbr) hKz
      _ = K * (a.length + 1) * (P + 1) := by ring
      _ = (100 * (Ke + Kz + 1)) * (a.length + 1) * (P + 1) := by rw [hK]
  refine KL.conseq main (comb qel)
    (fun vs => vs = ofList (a.map cfxVal) :: ofList (b.map cfxVal) :: rest)
    (fun vs => vs = [cvecVal a, cvecVal b] ++ rest)
    (fun _ out => out = ofList ((buAddV a b).map cfxVal) :: rest)
    (fun _ out => out = [cvecVal (buAddV a b)] ++ rest)
    (fun _ => (a.map cfxVal).length * (Ke * (P + 1) + Kz * (2 * P + 4 + 1)) + Kz)
    (fun _ => 100 * (Ke + Kz + 1) * (a.length + 1) * (P + 1))
    hzw ?_ ?_ ?_
  · intro vs h
    rw [h]
    rfl
  · intro vs out _ hq
    rw [hq]
    rfl
  · intro vs _
    exact hcost

/-! ## 4.  the assembly -/

theorem buQWcolWord_of (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib)
    (hmul : ∃ (q : HvdH.Cmd) (Kc : ℕ),
      ∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ) (p : ℕ) (w : List ℤ) (v : List (ℤ × ℤ)),
        Monotone Cm → HvdH.MulBelow main N Cm → 100 ≤ p → Kc * p < N →
        w.length = v.length → (∀ y ∈ w, HvdH.isz y ≤ p + 3) →
        (∀ y ∈ v, HvdH.isz y.1 ≤ p + 5 ∧ HvdH.isz y.2 ≤ p + 5) →
        Work.Resample.Pipe main q [HvdH.ofList (w.map HvdH.Val.int), HvdH.cvecVal v]
          [HvdH.cvecVal (Work.Resample.buMulCol w v)]
          (Kc * (w.length + 1) * (Cm (Kc * p) + p + 1)))
    (hadd : ∃ (q : HvdH.Cmd) (Kc : ℕ),
      ∀ (main : HvdH.Cmd) (P : ℕ) (a b : List (ℤ × ℤ)),
        a.length = b.length →
        (∀ z ∈ a, HvdH.isz z.1 ≤ P ∧ HvdH.isz z.2 ≤ P) →
        (∀ z ∈ b, HvdH.isz z.1 ≤ P ∧ HvdH.isz z.2 ≤ P) →
        Work.Resample.Pipe main q [HvdH.cvecVal a, HvdH.cvecVal b]
          [HvdH.cvecVal (Work.Resample.buAddV a b)] (Kc * (a.length + 1) * (P + 1))) :
    ∃ (q : HvdH.Cmd) (Kc : ℕ),
    ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hp : 100 ≤ p)
      (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ),
      Monotone Cm → HvdH.MulBelow main N Cm → Kc * p < N →
      ∀ (h : ℤ) (w : List ℤ) (hh : h ∈ Work.Resample.egHs (Work.Resample.egM p α))
        (hw : w = Work.Resample.buColL (Work.Resample.buWt p α s t) s h)
        (hwisz : ∀ y ∈ w, HvdH.isz y ≤ p + 3)
        (hwlen : w.length = s)
        (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (v z acc : List (ℤ × ℤ))
        (hv : v.length = s) (hz : z.length = s) (ha : acc.length = s)
        (hvsz : ∀ y ∈ v, HvdH.isz y.1 ≤ p + 5 ∧ HvdH.isz y.2 ≤ p + 5)
        (hzsz : ∀ y ∈ z, HvdH.isz y.1 ≤ 2 * p + 8 ∧ HvdH.isz y.2 ≤ 2 * p + 8)
        (haccsz : ∀ y ∈ acc, HvdH.isz y.1 ≤ p + 5 ∧ HvdH.isz y.2 ≤ p + 5),
      Work.Resample.Pipe main q
        [HvdH.Val.cons (HvdH.Val.int h) (HvdH.ofList (w.map HvdH.Val.int)), HvdH.cvecVal z,
          HvdH.Val.int σ, HvdH.cvecVal v, HvdH.cvecVal acc, HvdH.Val.int (s : ℤ),
          HvdH.Val.int (p : ℤ)]
        [HvdH.cvecVal (Work.Resample.buAddV z (Work.Resample.buMulCol w
            (Work.Resample.buRot ((h % (s : ℤ)).toNat) v))),
          HvdH.Val.int σ, HvdH.cvecVal v, HvdH.cvecVal acc, HvdH.Val.int (s : ℤ),
          HvdH.Val.int (p : ℤ)]
        (Kc * (s + 1) * (Cm (Kc * p) + p + 1)) := by
  obtain ⟨qmul, Kmul, hmul'⟩ := hmul
  obtain ⟨qadd, Kadd, hadd'⟩ := hadd
  obtain ⟨uncP, Kunc, hunc⟩ := KL.unconsV
  obtain ⟨pickP, Kpick, hpick⟩ := KL.pick
  obtain ⟨swapP, Kswap, hswap⟩ := KL.swap
  obtain ⟨fmodP, Kfmod, hfmod⟩ := IL.fmod
  obtain ⟨qrot, Krot, hrot⟩ := buQWr1Rot KL LL
  let KS : ℕ := Kunc + Kpick + Kswap + Kfmod + Krot + Kmul + Kadd + 100
  let Kc : ℕ := Kmul + 10000000 * KS + 1000
  have hKunc : Kunc ≤ KS := by simp only [KS]; omega
  have hKpick : Kpick ≤ KS := by simp only [KS]; omega
  have hKswap : Kswap ≤ KS := by simp only [KS]; omega
  have hKfmod : Kfmod ≤ KS := by simp only [KS]; omega
  have hKrot : Krot ≤ KS := by simp only [KS]; omega
  have hKmul : Kmul ≤ KS := by simp only [KS]; omega
  have hKadd : Kadd ≤ KS := by simp only [KS]; omega
  have hKmulKc : Kmul ≤ Kc := by simp only [Kc]; omega
  have hKc : Kc = Kmul + 10000000 * KS + 1000 := rfl
  refine ⟨Cmd.seq uncP (Cmd.seq (pickP 6) (Cmd.seq swapP (Cmd.seq fmodP (Cmd.seq (pickP 4)
    (Cmd.seq swapP (Cmd.seq qrot (Cmd.seq swapP (Cmd.seq qmul (Cmd.seq swapP qadd))))))))),
    Kc, ?_⟩
  intro p α s t hs hp main N Cm hmono hmb hKN
  intro h w hh hw hwisz hwlen σ hσ v z acc hv hz ha hvsz hzsz haccsz
  set Wh : Val := ofList (w.map Val.int) with hWh
  set Zl : Val := cvecVal z with hZl
  set Sg : Val := Val.int σ with hSg
  set Vl : Val := cvecVal v with hVl
  set Ac : Val := cvecVal acc with hAc
  set Sv : Val := Val.int (s : ℤ) with hSv
  set Pv : Val := Val.int (p : ℤ) with hPv
  set kk : ℕ := (h % (s : ℤ)).toNat with hkk
  set E : ℕ := (s + 1) * (p + 1) with hE
  set M : ℕ := 3 * s * (6 * p + 29) + s + p + 100 with hM
  have hE1 : 1 ≤ E := by
    rw [hE]
    exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos s) (Nat.succ_pos p))
  have hMm : M ≤ 100 * E := by
    rw [hM, hE]
    nlinarith [Nat.zero_le s, Nat.zero_le p]
  have hsizeS : s.size ≤ s := Nat.size_le.mpr (Nat.lt_two_pow_self (n := s))
  have hiszh : isz h ≤ p + 3 := by
    have h1 : h.natAbs ≤ egM p α := (buQWhs (egM p α)).2.2.2.2.1 h hh
    have h2 := Work.Fx.isz_le_of_natAbs_lt (a := h) (n := p + 1)
      (lt_of_le_of_lt (le_trans h1 (buQT_egM_le p α)) (Nat.lt_two_pow_self (n := p + 1)))
    omega
  have hsizSZ : isz (s : ℤ) ≤ s + 2 := by
    have h : (s : ℤ).natAbs = s := Int.natAbs_natCast s
    simp only [isz, h]
    omega
  have hpizZ : isz (p : ℤ) ≤ p + 2 := by
    have h : (p : ℤ).natAbs = p := Int.natAbs_natCast p
    have h2 : p.size ≤ p := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p))
    simp only [isz, h]
    omega
  have hkE : Int.fmod h (s : ℤ) = ((kk : ℕ) : ℤ) := by
    rw [hkk, Int.fmod_eq_emod, if_pos (Or.inl (show (0 : ℤ) ≤ (s : ℤ) by positivity))]
    simp only [add_zero]
    exact (Int.toNat_of_nonneg (Int.emod_nonneg h (by omega))).symm
  have hklt : kk < s := by
    have h1 : (0 : ℤ) ≤ h % (s : ℤ) := Int.emod_nonneg h (by omega)
    have h2 : h % (s : ℤ) < (s : ℤ) := Int.emod_lt_of_pos h (by omega)
    have h3 : (((h % (s : ℤ)).toNat : ℕ) : ℤ) = h % (s : ℤ) := Int.toNat_of_nonneg h1
    rw [hkk]
    omega
  have hiszK : isz ((kk : ℕ) : ℤ) ≤ s + 2 := by
    have h1 : (((kk : ℕ) : ℤ)).natAbs ≤ s := by
      have := hklt
      simp only [Int.natAbs_natCast]
      omega
    have h2 : (((kk : ℕ) : ℤ)).natAbs.size ≤ s :=
      Nat.size_le.mpr (lt_of_le_of_lt h1 (Nat.lt_two_pow_self (n := s)))
    simp only [isz]
    omega
  have hMh : vsz (Val.int h) ≤ M := by
    rw [Work.Fx.vsz_int, hM]
    omega
  have hMWh : vsz Wh ≤ M := by
    rw [hWh]
    have h1 : vsz (ofList (w.map Val.int)) = w.length + 1 + (w.map isz).sum := by
      rw [show ofList (w.map Val.int) = zl w from rfl]
      exact buQT_vsz_zl w
    rw [h1, hwlen, hM]
    have h2 : (w.map isz).sum ≤ s * (p + 3) := by
      have h3 := buQT_sum_le_length_mul (l := w.map isz) (M := p + 3) (fun y hy => by
        rcases List.mem_map.mp hy with ⟨c, hc, rfl⟩
        exact hwisz c hc)
      rwa [List.length_map, hwlen] at h3
    nlinarith [h2, Nat.zero_le s, Nat.zero_le p]
  have hMZ : vsz Zl ≤ M := by
    rw [hZl]
    have h1 : vsz (cvecVal z) ≤ 3 * z.length * (2 * p + 8 + 1) + 1 := buQT_vsz_cvecVal hzsz
    rw [hz] at h1
    rw [hM]
    nlinarith [h1, Nat.zero_le s, Nat.zero_le p]
  have hMSg : vsz Sg ≤ M := by
    rw [hSg, Work.Fx.vsz_int, hM]
    have h3 : isz σ ≤ 3 := by rcases hσ with rfl | rfl <;> decide
    omega
  have hMV : vsz Vl ≤ M := by
    rw [hVl]
    have h1 : vsz (cvecVal v) ≤ 3 * v.length * (p + 5 + 1) + 1 := buQT_vsz_cvecVal hvsz
    rw [hv] at h1
    rw [hM]
    nlinarith [h1, Nat.zero_le s, Nat.zero_le p]
  have hMAc : vsz Ac ≤ M := by
    rw [hAc]
    have h1 : vsz (cvecVal acc) ≤ 3 * acc.length * (p + 5 + 1) + 1 := buQT_vsz_cvecVal haccsz
    rw [ha] at h1
    rw [hM]
    nlinarith [h1, Nat.zero_le s, Nat.zero_le p]
  have hMSv : vsz Sv ≤ M := by
    rw [hSv, Work.Fx.vsz_int, hM]
    have := hsizSZ
    omega
  have hMPv : vsz Pv ≤ M := by
    rw [hPv, Work.Fx.vsz_int, hM]
    have := hpizZ
    omega
  have hMK : vsz (Val.int ((kk : ℕ) : ℤ)) ≤ M := by
    rw [Work.Fx.vsz_int, hM]
    have := hiszK
    omega
  have hrotle : ∀ y ∈ buRot kk v, isz y.1 ≤ p + 5 ∧ isz y.2 ≤ p + 5 := by
    intro y hy
    rw [buRot] at hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hvsz y (List.mem_of_mem_drop hy)
    · exact hvsz y (List.mem_of_mem_take hy)
  have hMVrot : vsz (cvecVal (buRot kk v)) ≤ M := by
    have h1 : vsz (cvecVal (buRot kk v)) ≤ 3 * (buRot kk v).length * (p + 5 + 1) + 1 :=
      buQT_vsz_cvecVal hrotle
    rw [buRot_length, hv] at h1
    rw [hM]
    nlinarith [h1, Nat.zero_le s, Nat.zero_le p]
  have hlenm : (buMulCol w (buRot kk v)).length = s := by
    rw [buMulCol_length, buRot_length, hv, hwlen, Nat.min_self]
  have hMmulcol : ∀ y ∈ buMulCol w (buRot kk v), isz y.1 ≤ 2 * p + 8 ∧ isz y.2 ≤ 2 * p + 8 := by
    intro y hy
    simp only [buMulCol, List.mem_map] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨hc, hb⟩ := buQWcm_mem_zip ha
    have h1 : isz a.1 ≤ p + 3 := hwisz a.1 hc
    have h2 : isz a.2.1 ≤ p + 5 := (hrotle a.2 hb).1
    have h3 : isz a.2.2 ≤ p + 5 := (hrotle a.2 hb).2
    exact ⟨buQWcol_isz_mul_small h1 h2, buQWcol_isz_mul_small h1 h3⟩
  have hMMv : vsz (cvecVal (buMulCol w (buRot kk v))) ≤ M := by
    have h1 : vsz (cvecVal (buMulCol w (buRot kk v)))
        ≤ 3 * (buMulCol w (buRot kk v)).length * (2 * p + 8 + 1) + 1 :=
      buQT_vsz_cvecVal hMmulcol
    rw [hlenm] at h1
    rw [hM]
    nlinarith [h1, Nat.zero_le s, Nat.zero_le p]
  have hMz : ∀ y ∈ buAddV z (buMulCol w (buRot kk v)), isz y.1 ≤ 2 * p + 9 ∧ isz y.2 ≤ 2 * p + 9 := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := List.mem_iff_getElem.mp hy
    rw [← hyi]
    have habs : (buAddV z (buMulCol w (buRot kk v))).length = s := by
      rw [buAddV_length, hz, hlenm, Nat.min_self]
    have his : i < s := by rw [← habs]; exact hi
    have hzi : i < z.length := by rw [hz]; exact his
    have hmi : i < (buMulCol w (buRot kk v)).length := by rw [hlenm]; exact his
    have hgoal : (buAddV z (buMulCol w (buRot kk v)))[i]
        = ((z.getD i (0, 0)).1 + ((buMulCol w (buRot kk v)).getD i (0, 0)).1,
           (z.getD i (0, 0)).2 + ((buMulCol w (buRot kk v)).getD i (0, 0)).2) := by
      rw [← List.getD_eq_getElem (buAddV z (buMulCol w (buRot kk v))) (0, 0) hi]
      exact buAddV_getD z (buMulCol w (buRot kk v)) i hzi hmi
    rw [hgoal]
    have hz1 : isz (z.getD i (0, 0)).1 ≤ 2 * p + 8 := by
      rw [List.getD_eq_getElem z (0, 0) hzi]
      exact (hzsz _ (List.getElem_mem hzi)).1
    have hz2 : isz (z.getD i (0, 0)).2 ≤ 2 * p + 8 := by
      rw [List.getD_eq_getElem z (0, 0) hzi]
      exact (hzsz _ (List.getElem_mem hzi)).2
    have hm1 : isz ((buMulCol w (buRot kk v)).getD i (0, 0)).1 ≤ 2 * p + 8 := by
      rw [List.getD_eq_getElem (buMulCol w (buRot kk v)) (0, 0) hmi]
      exact (hMmulcol _ (List.getElem_mem hmi)).1
    have hm2 : isz ((buMulCol w (buRot kk v)).getD i (0, 0)).2 ≤ 2 * p + 8 := by
      rw [List.getD_eq_getElem (buMulCol w (buRot kk v)) (0, 0) hmi]
      exact (hMmulcol _ (List.getElem_mem hmi)).2
    exact ⟨buQWcol_isz_add_small hz1 hm1, buQWcol_isz_add_small hz2 hm2⟩
  have hMZc : vsz (cvecVal (buAddV z (buMulCol w (buRot kk v)))) ≤ M := by
    have h1 : vsz (cvecVal (buAddV z (buMulCol w (buRot kk v))))
        ≤ 3 * (buAddV z (buMulCol w (buRot kk v))).length * (2 * p + 9 + 1) + 1 :=
      buQT_vsz_cvecVal hMz
    rw [buAddV_length, hz, hlenm, Nat.min_self] at h1
    rw [hM]
    nlinarith [h1, Nat.zero_le s, Nat.zero_le p]
  have hW8 : ∀ v ∈ ([Val.int h, Wh, Zl, Sg, Vl, Ac, Sv, Pv] : List Val), vsz v ≤ M := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hMh, hMWh, hMZ, hMSg, hMV, hMAc, hMSv, hMPv]
  have hW9 : ∀ v ∈ ([Val.int ((kk : ℕ) : ℤ), Wh, Zl, Sg, Vl, Ac, Sv, Pv] : List Val), vsz v ≤ M := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hMK, hMWh, hMZ, hMSg, hMV, hMAc, hMSv, hMPv]
  have hX2 : Work.Fx.szl (([Val.int h, Wh, Zl, Sg, Vl, Ac, Sv, Pv] : List Val).take (6 + 1))
      ≤ 7 * M := by
    have h := buQW_szl_le_of (A := [Val.int h, Wh, Zl, Sg, Vl, Ac, Sv, Pv]) (k := 6) M hW8
    simpa using h
  have hX5 : Work.Fx.szl (([Val.int ((kk : ℕ) : ℤ), Wh, Zl, Sg, Vl, Ac, Sv, Pv] : List Val).take (4 + 1))
      ≤ 5 * M := by
    have h := buQW_szl_le_of (A := [Val.int ((kk : ℕ) : ℤ), Wh, Zl, Sg, Vl, Ac, Sv, Pv])
      (k := 4) M hW9
    simpa using h
  have hb1 : Kunc ≤ KS * (1000000 * E) := by
    have h := buQWcol_cheapLe (K := Kunc) (KS := KS) (A := 1) (E := E) hKunc
      (by omega : 1 ≤ 100000 * E)
    simpa using h
  have hb2 : Kpick * (6 + 1)
      * (Work.Fx.szl (([Val.int h, Wh, Zl, Sg, Vl, Ac, Sv, Pv] : List Val).take (6 + 1)) + 1)
      ≤ KS * (1000000 * E) := by
    have hA : (6 + 1)
        * (Work.Fx.szl (([Val.int h, Wh, Zl, Sg, Vl, Ac, Sv, Pv] : List Val).take (6 + 1)) + 1)
        ≤ 100000 * E := by
      have h1 := hX2
      have h2 := hMm
      have h3 := hE1
      nlinarith
    calc Kpick * (6 + 1)
          * (Work.Fx.szl (([Val.int h, Wh, Zl, Sg, Vl, Ac, Sv, Pv] : List Val).take (6 + 1)) + 1)
        = Kpick * ((6 + 1)
          * (Work.Fx.szl (([Val.int h, Wh, Zl, Sg, Vl, Ac, Sv, Pv] : List Val).take (6 + 1)) + 1)) := by
            ring
      _ ≤ KS * (1000000 * E) := buQWcol_cheapLe hKpick hA
  have hb3 : Kswap * (vsz Sv + vsz (Val.int h) + 1) ≤ KS * (1000000 * E) := by
    have hA : vsz Sv + vsz (Val.int h) + 1 ≤ 100000 * E := by
      have h1 := hMSv
      have h2 := hMh
      have h3 := hMm
      have h4 := hE1
      nlinarith
    exact buQWcol_cheapLe (K := Kswap) (A := vsz Sv + vsz (Val.int h) + 1) hKswap hA
  have hb4 : Kfmod * isz h * isz (s : ℤ) ≤ KS * (1000000 * E) := by
    have hA : isz h * isz (s : ℤ) ≤ 100000 * E := by
      have h1 := hiszh
      have h2 := hsizSZ
      have h3 := hE1
      nlinarith [Nat.zero_le s, Nat.zero_le p]
    calc Kfmod * isz h * isz (s : ℤ) = Kfmod * (isz h * isz (s : ℤ)) := by ring
      _ ≤ KS * (1000000 * E) :=
          buQWcol_cheapLe (K := Kfmod) (A := isz h * isz (s : ℤ)) hKfmod hA
  have hb5 : Kpick * (4 + 1)
      * (Work.Fx.szl (([Val.int ((kk : ℕ) : ℤ), Wh, Zl, Sg, Vl, Ac, Sv, Pv] : List Val).take (4 + 1)) + 1)
      ≤ KS * (1000000 * E) := by
    have hA : (4 + 1)
        * (Work.Fx.szl (([Val.int ((kk : ℕ) : ℤ), Wh, Zl, Sg, Vl, Ac, Sv, Pv] : List Val).take (4 + 1)) + 1)
        ≤ 100000 * E := by
      have h1 := hX5
      have h2 := hMm
      have h3 := hE1
      nlinarith
    calc Kpick * (4 + 1)
          * (Work.Fx.szl (([Val.int ((kk : ℕ) : ℤ), Wh, Zl, Sg, Vl, Ac, Sv, Pv] : List Val).take (4 + 1)) + 1)
        = Kpick * ((4 + 1)
          * (Work.Fx.szl (([Val.int ((kk : ℕ) : ℤ), Wh, Zl, Sg, Vl, Ac, Sv, Pv] : List Val).take (4 + 1)) + 1)) := by
            ring
      _ ≤ KS * (1000000 * E) := buQWcol_cheapLe hKpick hA
  have hb6 : Kswap * (vsz Vl + vsz (Val.int ((kk : ℕ) : ℤ)) + 1) ≤ KS * (1000000 * E) := by
    have hA : vsz Vl + vsz (Val.int ((kk : ℕ) : ℤ)) + 1 ≤ 100000 * E := by
      have h1 := hMV
      have h2 := hMK
      have h3 := hMm
      have h4 := hE1
      nlinarith
    exact buQWcol_cheapLe (K := Kswap) (A := vsz Vl + vsz (Val.int ((kk : ℕ) : ℤ)) + 1) hKswap hA
  have hb7 : Krot * ((s + 1) * (p + 5 + 1) + (isz ((kk : ℕ) : ℤ) + 1))
      ≤ KS * (1000000 * E) := by
    have hA : (s + 1) * (p + 5 + 1) + (isz ((kk : ℕ) : ℤ) + 1) ≤ 100000 * E := by
      have h1 := hiszK
      have h2 := hE1
      rw [hE]
      nlinarith [Nat.zero_le s, Nat.zero_le p]
    exact buQWcol_cheapLe (K := Krot) (A := (s + 1) * (p + 5 + 1) + (isz ((kk : ℕ) : ℤ) + 1)) hKrot hA
  have hb8 : Kswap * (vsz (cvecVal (buRot kk v)) + vsz Wh + 1) ≤ KS * (1000000 * E) := by
    have hA : vsz (cvecVal (buRot kk v)) + vsz Wh + 1 ≤ 100000 * E := by
      have h1 := hMWh
      have h2 := hMVrot
      have h3 := hMm
      have h4 := hE1
      nlinarith
    exact buQWcol_cheapLe (K := Kswap) (A := vsz (cvecVal (buRot kk v)) + vsz Wh + 1) hKswap hA
  have hb10 : Kswap * (vsz (cvecVal (buMulCol w (buRot kk v))) + vsz Zl + 1)
      ≤ KS * (1000000 * E) := by
    have hA : vsz (cvecVal (buMulCol w (buRot kk v))) + vsz Zl + 1 ≤ 100000 * E := by
      have h1 := hMZ
      have h2 := hMMv
      have h3 := hMm
      have h4 := hE1
      nlinarith
    exact buQWcol_cheapLe (K := Kswap)
      (A := vsz (cvecVal (buMulCol w (buRot kk v))) + vsz Zl + 1) hKswap hA
  have hb11 : Kadd * (s + 1) * (2 * p + 8 + 1) ≤ KS * (1000000 * E) := by
    have hA : (s + 1) * (2 * p + 8 + 1) ≤ 100000 * E := by
      have h2 := hE1
      rw [hE]
      nlinarith [Nat.zero_le s, Nat.zero_le p]
    calc Kadd * (s + 1) * (2 * p + 8 + 1) = Kadd * ((s + 1) * (2 * p + 8 + 1)) := by ring
      _ ≤ KS * (1000000 * E) :=
          buQWcol_cheapLe (K := Kadd) (A := (s + 1) * (2 * p + 8 + 1)) hKadd hA
  have hwlenrot : w.length = (buRot kk v).length := by
    rw [buRot_length, hv]
    exact hwlen
  have hKNmul : Kmul * p < N := lt_of_le_of_lt (Nat.mul_le_mul_right p hKmulKc) hKN
  have hlenadd : z.length = (buMulCol w (buRot kk v)).length := by
    rw [hz, hlenm]
  have hrot0 : (0 : ℤ) ≤ Int.fmod h (s : ℤ) := by rw [hkE]; exact Int.natCast_nonneg _
  have hrottoNat : (Int.fmod h (s : ℤ)).toNat = kk := by rw [hkE, Int.toNat_natCast]
  have hrotlt : (Int.fmod h (s : ℤ)).toNat < s := by rw [hrottoNat]; exact hklt
  have s1 : Pipe main uncP
      (Val.cons (Val.int h) Wh :: [Zl, Sg, Vl, Ac, Sv, Pv])
      (Val.int h :: Wh :: [Zl, Sg, Vl, Ac, Sv, Pv]) Kunc :=
    Pipe.unconsVA (main := main) hunc (a := Val.int h) (b := Wh) (T := [Zl, Sg, Vl, Ac, Sv, Pv])
  have s2 : Pipe main (pickP 6)
      [Val.int h, Wh, Zl, Sg, Vl, Ac, Sv, Pv]
      [Sv, Val.int h, Wh, Zl, Sg, Vl, Ac, Sv, Pv]
      (Kpick * (6 + 1)
        * (Work.Fx.szl (([Val.int h, Wh, Zl, Sg, Vl, Ac, Sv, Pv] : List Val).take (6 + 1)) + 1)) := by
    have hpk := Pipe.pick (main := main) hpick
      (A := [Val.int h, Wh, Zl, Sg, Vl, Ac, Sv, Pv]) (k := 6) (by simp)
    exact Pipe.rw hpk (B' := [Sv, Val.int h, Wh, Zl, Sg, Vl, Ac, Sv, Pv]) rfl
  have s3 : Pipe main swapP
      [Sv, Val.int h, Wh, Zl, Sg, Vl, Ac, Sv, Pv]
      [Val.int h, Sv, Wh, Zl, Sg, Vl, Ac, Sv, Pv]
      (Kswap * (vsz Sv + vsz (Val.int h) + 1)) := by
    simpa only [List.cons_append, List.nil_append] using
      (Pipe.appendTail [Wh, Zl, Sg, Vl, Ac, Sv, Pv]
        (Pipe.swap main hswap Sv (Val.int h)))
  have s4 : Pipe main fmodP
      [Val.int h, Sv, Wh, Zl, Sg, Vl, Ac, Sv, Pv]
      [Val.int ((kk : ℕ) : ℤ), Wh, Zl, Sg, Vl, Ac, Sv, Pv]
      (Kfmod * isz h * isz (s : ℤ)) := by
    have h : Pipe main fmodP [Val.int h, Val.int (s : ℤ)] [Val.int (Int.fmod h (s : ℤ))]
        (Kfmod * isz h * isz (s : ℤ)) :=
      Pipe.binOp (main := main) (prog := fmodP) (hfmod main)
        (show (0 : ℤ) < (s : ℤ) by omega)
    rw [hkE] at h
    simpa only [List.cons_append, List.nil_append] using
      (Pipe.appendTail [Wh, Zl, Sg, Vl, Ac, Sv, Pv] h)
  have s5 : Pipe main (pickP 4)
      [Val.int ((kk : ℕ) : ℤ), Wh, Zl, Sg, Vl, Ac, Sv, Pv]
      [Vl, Val.int ((kk : ℕ) : ℤ), Wh, Zl, Sg, Vl, Ac, Sv, Pv]
      (Kpick * (4 + 1)
        * (Work.Fx.szl (([Val.int ((kk : ℕ) : ℤ), Wh, Zl, Sg, Vl, Ac, Sv, Pv] : List Val).take (4 + 1)) + 1)) := by
    have hpk := Pipe.pick (main := main) hpick
      (A := [Val.int ((kk : ℕ) : ℤ), Wh, Zl, Sg, Vl, Ac, Sv, Pv]) (k := 4) (by simp)
    exact Pipe.rw hpk (B' := [Vl, Val.int ((kk : ℕ) : ℤ), Wh, Zl, Sg, Vl, Ac, Sv, Pv]) rfl
  have s6 : Pipe main swapP
      [Vl, Val.int ((kk : ℕ) : ℤ), Wh, Zl, Sg, Vl, Ac, Sv, Pv]
      [Val.int ((kk : ℕ) : ℤ), Vl, Wh, Zl, Sg, Vl, Ac, Sv, Pv]
      (Kswap * (vsz Vl + vsz (Val.int ((kk : ℕ) : ℤ)) + 1)) := by
    simpa only [List.cons_append, List.nil_append] using
      (Pipe.appendTail [Wh, Zl, Sg, Vl, Ac, Sv, Pv]
        (Pipe.swap main hswap Vl (Val.int ((kk : ℕ) : ℤ))))
  have s7 : Pipe main qrot
      [Val.int ((kk : ℕ) : ℤ), Vl, Wh, Zl, Sg, Vl, Ac, Sv, Pv]
      [cvecVal (buRot kk v), Wh, Zl, Sg, Vl, Ac, Sv, Pv]
      (Krot * ((s + 1) * (p + 5 + 1) + (isz ((kk : ℕ) : ℤ) + 1))) := by
    have hrot' := hrot main s (Int.fmod h (s : ℤ)) v (p + 5) hrot0 hrotlt hv hvsz
    rw [hrottoNat, hkE] at hrot'
    simpa only [List.cons_append, List.nil_append] using
      (Pipe.appendTail [Wh, Zl, Sg, Vl, Ac, Sv, Pv] hrot')
  have s8 : Pipe main swapP
      [cvecVal (buRot kk v), Wh, Zl, Sg, Vl, Ac, Sv, Pv]
      [Wh, cvecVal (buRot kk v), Zl, Sg, Vl, Ac, Sv, Pv]
      (Kswap * (vsz (cvecVal (buRot kk v)) + vsz Wh + 1)) := by
    simpa only [List.cons_append, List.nil_append] using
      (Pipe.appendTail [Zl, Sg, Vl, Ac, Sv, Pv]
        (Pipe.swap main hswap (cvecVal (buRot kk v)) Wh))
  have s9 : Pipe main qmul
      [Wh, cvecVal (buRot kk v), Zl, Sg, Vl, Ac, Sv, Pv]
      [cvecVal (buMulCol w (buRot kk v)), Zl, Sg, Vl, Ac, Sv, Pv]
      (Kmul * (s + 1) * (Cm (Kmul * p) + p + 1)) := by
    have h := hmul' main N Cm p w (buRot kk v) hmono hmb hp hKNmul hwlenrot hwisz hrotle
    rw [hwlen] at h
    simpa only [List.cons_append, List.nil_append] using
      (Pipe.appendTail [Zl, Sg, Vl, Ac, Sv, Pv] h)
  have s10 : Pipe main swapP
      [cvecVal (buMulCol w (buRot kk v)), Zl, Sg, Vl, Ac, Sv, Pv]
      [Zl, cvecVal (buMulCol w (buRot kk v)), Sg, Vl, Ac, Sv, Pv]
      (Kswap * (vsz (cvecVal (buMulCol w (buRot kk v))) + vsz Zl + 1)) := by
    simpa only [List.cons_append, List.nil_append] using
      (Pipe.appendTail [Sg, Vl, Ac, Sv, Pv]
        (Pipe.swap main hswap (cvecVal (buMulCol w (buRot kk v))) Zl))
  have s11 : Pipe main qadd
      [Zl, cvecVal (buMulCol w (buRot kk v)), Sg, Vl, Ac, Sv, Pv]
      [cvecVal (buAddV z (buMulCol w (buRot kk v))), Sg, Vl, Ac, Sv, Pv]
      (Kadd * (s + 1) * (2 * p + 8 + 1)) := by
    have h := hadd' main (2 * p + 8) z (buMulCol w (buRot kk v)) hlenadd hzsz hMmulcol
    rw [hz] at h
    simpa only [List.cons_append, List.nil_append] using
      (Pipe.appendTail [Sg, Vl, Ac, Sv, Pv] h)
  have hchain := Pipe.comp s1 (Pipe.comp s2 (Pipe.comp s3 (Pipe.comp s4 (Pipe.comp s5
    (Pipe.comp s6 (Pipe.comp s7 (Pipe.comp s8 (Pipe.comp s9 (Pipe.comp s10 s11)))))))))
  have hCm : Cm (Kmul * p) ≤ Cm (Kc * p) := hmono (Nat.mul_le_mul_right p hKmulKc)
  have hcost := buQWcol_cost (Kmul := Kmul) (Kc := Kc) (KS := KS) (s := s) (p := p)
    (CmKmul := Cm (Kmul * p)) (CmKc := Cm (Kc * p))
    (h1 := hb1) (h2 := hb2) (h3 := hb3) (h4 := hb4) (h5 := hb5) (h6 := hb6)
    (h7 := hb7) (h8 := hb8) (h9 := le_rfl) (h10 := hb10) (h11 := hb11)
    (hCm := hCm) (hKc := hKc)
  exact Pipe.le hchain hcost

/-! ## 5.  the target -/

theorem buQWcolWord (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib) :
    ∃ (q : HvdH.Cmd) (Kc : ℕ),
    ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hp : 100 ≤ p)
      (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ),
      Monotone Cm → HvdH.MulBelow main N Cm → Kc * p < N →
      ∀ (h : ℤ) (w : List ℤ) (hh : h ∈ Work.Resample.egHs (Work.Resample.egM p α))
        (hw : w = Work.Resample.buColL (Work.Resample.buWt p α s t) s h)
        (hwisz : ∀ y ∈ w, HvdH.isz y ≤ p + 3)
        (hwlen : w.length = s)
        (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (v z acc : List (ℤ × ℤ))
        (hv : v.length = s) (hz : z.length = s) (ha : acc.length = s)
        (hvsz : ∀ y ∈ v, HvdH.isz y.1 ≤ p + 5 ∧ HvdH.isz y.2 ≤ p + 5)
        (hzsz : ∀ y ∈ z, HvdH.isz y.1 ≤ 2 * p + 8 ∧ HvdH.isz y.2 ≤ 2 * p + 8)
        (haccsz : ∀ y ∈ acc, HvdH.isz y.1 ≤ p + 5 ∧ HvdH.isz y.2 ≤ p + 5),
      Work.Resample.Pipe main q
        [HvdH.Val.cons (HvdH.Val.int h) (HvdH.ofList (w.map HvdH.Val.int)), HvdH.cvecVal z,
          HvdH.Val.int σ, HvdH.cvecVal v, HvdH.cvecVal acc, HvdH.Val.int (s : ℤ),
          HvdH.Val.int (p : ℤ)]
        [HvdH.cvecVal (Work.Resample.buAddV z (Work.Resample.buMulCol w
            (Work.Resample.buRot ((h % (s : ℤ)).toNat) v))),
          HvdH.Val.int σ, HvdH.cvecVal v, HvdH.cvecVal acc, HvdH.Val.int (s : ℤ),
          HvdH.Val.int (p : ℤ)]
        (Kc * (s + 1) * (Cm (Kc * p) + p + 1)) :=
  buQWcolWord_of KL IL LL (buQWcmMul KL IL) (buQWcmAdd KL IL)

end Work.Resample
