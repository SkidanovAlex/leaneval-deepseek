import Mathlib
import Submission.Work.Main.defs
import Submission.Work.Main.word.recoverElemB

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `Work.Main.word.recoverVec2`: the recovery word of the Harvey–van der Hoeven main step

Given a vector `zs ∈ C̃◦ⁿ` of fixed-point complex numbers, together with the parameters
`S ≤ 2^p` (the modulus of the cyclic convolution), the precision `p` and the chunk size `b`
(with `2b < p`), this file produces a StackLang word which replaces every coefficient
`cfxVal z = cons (int z.1) (int z.2)` of the vector by the integer

`recov S p b z = (S · z.1 + 2^(p-2b-1)).fdiv (2^(p-2b))`

(paper §5.3 step 7: `H'' = round(2^{2b} · S · w̃)`, computed here as the nearest integer to
`S · Re(w̃) · 2^{2b}`), in cost `K (n+1)(p+1)² + K`.

The word is `KernelLib.mapList` applied to the per-coefficient word `Work.Main.word.recoverElemB`
(with the parameters `S, p, b` staying below the list during the whole loop), and the vector of
results is read back from the list of values produced by `mapList` with the extraction lemma
`extract_list`.
-/

namespace Work.Main.word

open HvdH

/-! ## `WordR` plumbing -/

/-- Monotonicity (consequence rule) for `WordR`, proved directly from the definition. -/
theorem wordR_mono {main pr : Cmd} {P P' : List Val → Prop} {Q Q' : List Val → List Val → Prop}
    {C C' : List Val → ℕ} (h : WordR main pr P Q C) (h1 : ∀ vs, P' vs → P vs)
    (h2 : ∀ vs out, P' vs → Q vs out → Q' vs out) (h3 : ∀ vs, P' vs → C vs ≤ C' vs) :
    WordR main pr P' Q' C' := by
  intro vs hp s R hs
  obtain ⟨out, s', n, hQ, hev, hn, hl, hk⟩ := h vs (h1 vs hp) s R hs
  exact ⟨out, s', n, h2 vs out hp hQ, hev, le_trans hn (h3 vs hp), hl, hk⟩

/-- Sequential composition of two deterministic constant-cost `WordR`s. -/
theorem seqDet {main : Cmd} {q₁ q₂ : Cmd} {A B C' : List Val} {a b : ℕ}
    (h₁ : WordR main q₁ (fun vs => vs = A) (fun _ out => out = B) (fun _ => a))
    (h₂ : WordR main q₂ (fun vs => vs = B) (fun _ out => out = C') (fun _ => b)) :
    WordR main (.seq q₁ q₂) (fun vs => vs = A) (fun _ out => out = C') (fun _ => a + b) := by
  intro vs hvs s R hs
  rw [hvs] at hs
  obtain ⟨o₁, s₁, n₁, ho₁, he₁, hn₁, hl₁, hk₁⟩ := h₁ A rfl s R hs
  rw [ho₁] at hl₁
  obtain ⟨o₂, s₂, n₂, ho₂, he₂, hn₂, hl₂, hk₂⟩ := h₂ B rfl s₁ R hl₁
  exact ⟨o₂, s₂, n₁ + n₂, ho₂, Eval.seq he₁ he₂, Nat.add_le_add hn₁ hn₂, hl₂,
    fun k hk => by rw [hk₂ k hk, hk₁ k hk]⟩

/-! ## Elementary size bounds for values in the disc -/

private theorem natAbs_le_two_pow {p : ℕ} {z : ℤ} (h : z ^ 2 ≤ (4 : ℤ) ^ p) : z.natAbs ≤ 2 ^ p := by
  have h3 : ((z.natAbs : ℤ)) ^ 2 ≤ (((2 ^ p : ℕ)) : ℤ) ^ 2 := by
    have e : ((z.natAbs : ℤ)) ^ 2 = z ^ 2 := by
      rw [← Int.natCast_pow, ← Int.natAbs_pow, Int.natAbs_of_nonneg (sq_nonneg z)]
    have e2 : (((2 ^ p : ℕ) : ℤ)) ^ 2 = (4 : ℤ) ^ p := by
      have h1 : (((2 ^ p : ℕ) : ℤ)) = (2 : ℤ) ^ p := Int.natCast_pow 2 p
      rw [h1, ← pow_mul, mul_comm, pow_mul, show (4 : ℤ) = (2 : ℤ) ^ 2 by norm_num]
    rw [e, e2]
    exact h
  exact (Nat.pow_le_pow_iff_left (n := 2) (show (2 : ℕ) ≠ 0 by norm_num)).mp (by exact_mod_cast h3)

private theorem isz_le_of_natAbs_le {z : ℤ} {p : ℕ} (h : z.natAbs ≤ 2 ^ p) : isz z ≤ p + 3 := by
  have h1 : z.natAbs.size ≤ p + 1 := by
    rw [Nat.size_le]
    exact lt_of_le_of_lt h (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self p))
  simp only [isz]
  omega

theorem inDisc_fst_natAbs_le {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) : z.1.natAbs ≤ 2 ^ p := by
  apply natAbs_le_two_pow
  simp only [inDisc] at h
  nlinarith [sq_nonneg z.2]

theorem inDisc_snd_natAbs_le {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) : z.2.natAbs ≤ 2 ^ p := by
  apply natAbs_le_two_pow
  simp only [inDisc] at h
  nlinarith [sq_nonneg z.1]

theorem isz_fst_le {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) : isz z.1 ≤ p + 3 :=
  isz_le_of_natAbs_le (inDisc_fst_natAbs_le h)

theorem isz_snd_le {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) : isz z.2 ≤ p + 3 :=
  isz_le_of_natAbs_le (inDisc_snd_natAbs_le h)

theorem natAbs_natCast_le {p c : ℕ} (h : c ≤ 2 ^ p) : ((c : ℤ)).natAbs ≤ 2 ^ p := by
  rw [Int.natAbs_natCast]; exact h

theorem isz_le_of_le_two_pow {p c : ℕ} (h : c ≤ 2 ^ p) : isz ((c : ℤ)) ≤ p + 3 :=
  isz_le_of_natAbs_le (natAbs_natCast_le h)

theorem isz_int_le (p : ℕ) : isz ((p : ℤ)) ≤ p + 2 := by
  rw [isz, Int.natAbs_natCast]
  have h : p.size ≤ p := by
    rw [Nat.size_le]
    exact Nat.lt_two_pow_self
  omega

/-! ## The size of the recovered integer -/

theorem recov_natAbs_le {S p b : ℕ} (hb : 2 * b < p) (hS : S ≤ 2 ^ p) {z : ℤ × ℤ}
    (hz : inDisc p z) : (recov S p b z).natAbs ≤ 2 ^ (2 * p + 2) := by
  have hN1 : ((S : ℤ) * z.1 + (2 : ℤ) ^ (p - 2 * b - 1)).natAbs ≤ 2 ^ (2 * p + 1) := by
    have h1 : ((S : ℤ) * z.1).natAbs ≤ 2 ^ p * 2 ^ p := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      exact Nat.mul_le_mul hS (inDisc_fst_natAbs_le hz)
    have h2 : ((2 : ℤ) ^ (p - 2 * b - 1)).natAbs ≤ 2 ^ p := by
      rw [Int.natAbs_pow]
      have hcast : ((2 : ℤ)).natAbs = 2 := by norm_num
      rw [hcast]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : ((S : ℤ) * z.1 + (2 : ℤ) ^ (p - 2 * b - 1)).natAbs
        ≤ 2 ^ p * 2 ^ p + 2 ^ p :=
      le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add h1 h2)
    have hp : 2 ^ p * 2 ^ p = 2 ^ (2 * p) := by rw [← pow_add, two_mul]
    rw [hp] at h3
    have h4 : 2 ^ p ≤ 2 ^ (2 * p) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc _ ≤ 2 ^ (2 * p) + 2 ^ p := h3
      _ ≤ 2 ^ (2 * p) + 2 ^ (2 * p) := Nat.add_le_add_left h4 _
      _ = 2 ^ (2 * p + 1) := by rw [pow_succ']; ring
  have hN2pos : (0 : ℤ) < (2 : ℤ) ^ (p - 2 * b) := by positivity
  have hfin : ((S : ℤ) * z.1 + (2 : ℤ) ^ (p - 2 * b - 1)).fdiv ((2 : ℤ) ^ (p - 2 * b))
      = ((S : ℤ) * z.1 + (2 : ℤ) ^ (p - 2 * b - 1)) / ((2 : ℤ) ^ (p - 2 * b)) :=
    Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt hN2pos)
  have hlast : 2 ^ (2 * p + 1) + 1 ≤ 2 ^ (2 * p + 2) := by
    have hone : 1 ≤ 2 ^ (2 * p + 1) := Nat.one_le_two_pow
    have he : 2 ^ (2 * p + 2) = 2 ^ (2 * p + 1) * 2 := by
      rw [show 2 * p + 2 = 2 * p + 1 + 1 by omega, pow_succ]
    omega
  calc (recov S p b z).natAbs
      = (((S : ℤ) * z.1 + (2 : ℤ) ^ (p - 2 * b - 1)).fdiv ((2 : ℤ) ^ (p - 2 * b))).natAbs := rfl
    _ = (((S : ℤ) * z.1 + (2 : ℤ) ^ (p - 2 * b - 1)) / ((2 : ℤ) ^ (p - 2 * b))).natAbs := by
        rw [hfin]
    _ ≤ ((S : ℤ) * z.1 + (2 : ℤ) ^ (p - 2 * b - 1)).natAbs + 1 := by
        rw [Int.natAbs_ediv]
        have hd := Nat.div_le_self ((S : ℤ) * z.1 + (2 : ℤ) ^ (p - 2 * b - 1)).natAbs
          (((2 : ℤ) ^ (p - 2 * b)).natAbs)
        split <;> omega
    _ ≤ 2 ^ (2 * p + 2) := by omega

theorem isz_recov_le {S p b : ℕ} (hb : 2 * b < p) (hS : S ≤ 2 ^ p) {z : ℤ × ℤ}
    (hz : inDisc p z) : isz (recov S p b z) ≤ 2 * p + 5 := by
  have h := recov_natAbs_le hb hS hz
  have h2 : (recov S p b z).natAbs.size ≤ 2 * p + 3 := by
    rw [Nat.size_le]
    exact lt_of_le_of_lt h (Nat.pow_lt_pow_right (by norm_num) (by omega))
  simp only [isz]
  omega

/-! ## Extraction of the list of recovered integers -/

theorem cfxVal_inj' {a b : ℤ × ℤ} (h : cfxVal a = cfxVal b) : a = b := by
  have h' : a.1 = b.1 ∧ a.2 = b.2 := by
    simpa [cfxVal, Val.cons.injEq, Val.int.injEq] using h
  exact Prod.ext h'.1 h'.2

theorem forall₂_map_int (S p b : ℕ) :
    ∀ {zs : List (ℤ × ℤ)} {ys : List Val},
      List.Forall₂ (fun x y => ∃ z : ℤ × ℤ, x = cfxVal z ∧ y = Val.int (recov S p b z))
        (zs.map cfxVal) ys →
      ys = zs.map (fun z => Val.int (recov S p b z)) := by
  intro zs
  induction zs with
  | nil =>
      intro ys h
      cases h with
      | nil => rfl
  | cons z zs' ih =>
      intro ys h
      cases h with
      | cons hz hrest =>
          obtain ⟨z', hz', hy⟩ := hz
          have hzz : z = z' := cfxVal_inj' hz'
          rw [← hzz] at hy
          rw [hy, ih hrest, List.map_cons]

theorem extract_list {S p b : ℕ} {zs : List (ℤ × ℤ)} {ys : List Val}
    (h : List.Forall₂ (fun x y => ∃ z : ℤ × ℤ, x = cfxVal z ∧ y = Val.int (recov S p b z))
      (zs.map cfxVal) ys) :
    ∃ hs : List ℤ, ys = hs.map Val.int ∧ hs.length = zs.length ∧
      ∀ i < zs.length, hs.getD i 0 = recov S p b (zs.getD i (0, 0)) := by
  refine ⟨zs.map (fun z => recov S p b z), ?_, ?_, ?_⟩
  · rw [forall₂_map_int S p b h]
    simp
  · simp
  · intro i hi
    have h1 : (zs.map (fun z => recov S p b z)).getD i 0
        = recov S p b (zs.getD i (0, 0)) := by
      rw [List.getD_eq_getElem (hn := by rw [List.length_map]; exact hi), List.getElem_map,
        List.getD_eq_getElem (l := zs) (d := ((0 : ℤ), (0 : ℤ))) (hn := hi)]
    exact h1

/-! ## Cost arithmetic -/

theorem costAux (Ke Km len p : ℕ) :
    len * (Ke * (p + 1) * (p + 1) + Km * ((2 * p + 8) + 1)) + Km
      ≤ (Ke + 10 * Km + 1) * (len + 1) * (p + 1) * (p + 1) + (Ke + 10 * Km + 1) := by
  have hb : (2 * p + 8) + 1 ≤ 10 * ((p + 1) * (p + 1)) := by
    have hs : p + 1 ≤ (p + 1) * (p + 1) := by
      have h : (p + 1) * 1 ≤ (p + 1) * (p + 1) := Nat.mul_le_mul_left _ (by omega)
      rwa [Nat.mul_one] at h
    have h1 : 2 * p + 9 ≤ 10 * (p + 1) := by omega
    have h2 : 10 * (p + 1) ≤ 10 * ((p + 1) * (p + 1)) := Nat.mul_le_mul_left 10 hs
    omega
  have h1 : Ke * (p + 1) * (p + 1) + Km * ((2 * p + 8) + 1)
      ≤ (Ke + 10 * Km) * ((p + 1) * (p + 1)) := by
    have h2 : Km * ((2 * p + 8) + 1) ≤ Km * (10 * ((p + 1) * (p + 1))) :=
      Nat.mul_le_mul_left _ hb
    have h3 : Ke * (p + 1) * (p + 1) = Ke * ((p + 1) * (p + 1)) :=
      Nat.mul_assoc Ke (p + 1) (p + 1)
    rw [h3]
    calc Ke * ((p + 1) * (p + 1)) + Km * ((2 * p + 8) + 1)
        ≤ Ke * ((p + 1) * (p + 1)) + Km * (10 * ((p + 1) * (p + 1))) :=
          Nat.add_le_add_left h2 _
      _ = (Ke + 10 * Km) * ((p + 1) * (p + 1)) := by ring
  have h4 : len * ((Ke + 10 * Km) * ((p + 1) * (p + 1)))
      ≤ (Ke + 10 * Km) * (len + 1) * (p + 1) * (p + 1) := by
    have h5 : len * ((Ke + 10 * Km) * ((p + 1) * (p + 1)))
        ≤ (len + 1) * ((Ke + 10 * Km) * ((p + 1) * (p + 1))) :=
      Nat.mul_le_mul_right _ (by omega)
    calc _ ≤ (len + 1) * ((Ke + 10 * Km) * ((p + 1) * (p + 1))) := h5
      _ = (Ke + 10 * Km) * (len + 1) * (p + 1) * (p + 1) := by ring
  have h6 : (Ke + 10 * Km) * (len + 1) * (p + 1) * (p + 1)
      ≤ (Ke + 10 * Km + 1) * (len + 1) * (p + 1) * (p + 1) := by
    apply Nat.mul_le_mul_right
    apply Nat.mul_le_mul_right
    apply Nat.mul_le_mul_right
    omega
  calc len * (Ke * (p + 1) * (p + 1) + Km * ((2 * p + 8) + 1)) + Km
      ≤ len * ((Ke + 10 * Km) * ((p + 1) * (p + 1))) + Km :=
        Nat.add_le_add_right (Nat.mul_le_mul_left len h1) _
    _ ≤ (Ke + 10 * Km) * (len + 1) * (p + 1) * (p + 1) + Km := Nat.add_le_add_right h4 _
    _ ≤ (Ke + 10 * Km + 1) * (len + 1) * (p + 1) * (p + 1) + (Ke + 10 * Km + 1) :=
        Nat.add_le_add h6 (by omega)

/-! ## The vector-level recovery word -/

theorem recoverVec2 (hKer : HvdH.KernelLib) (hInt : HvdH.IntLib) (hLay : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (S p b : ℕ) (zs : List (ℤ × ℤ)) (rest : List HvdH.Val),
      2 * b < p → S ≤ 2 ^ p → HvdH.InDiscVec p zs.length zs →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.cvecVal zs :: HvdH.Val.int S :: HvdH.Val.int p :: HvdH.Val.int b :: rest)
        (fun vs out => (∃ (hs : List ℤ), vs = HvdH.cvecVal zs :: HvdH.Val.int S :: HvdH.Val.int p :: HvdH.Val.int b :: rest ∧
          out = HvdH.ofList (hs.map HvdH.Val.int) :: HvdH.Val.int S :: HvdH.Val.int p :: HvdH.Val.int b :: rest ∧
          hs.length = zs.length ∧ ∀ i < zs.length, hs.getD i 0 = recov S p b (zs.getD i (0,0))))
        (fun _ => K * (zs.length + 1) * (p + 1) * (p + 1) + K) := by
  obtain ⟨elemP, Ke, helem⟩ := recoverElemB hKer hInt
  obtain ⟨mapP, Km, hmap⟩ := hKer.mapList
  refine ⟨mapP elemP, Ke + 10 * Km + 1, ?_⟩
  intro main S p b zs rest h2b hS hdisc
  have hper : ∀ x, (∃ z : ℤ × ℤ, x = cfxVal z ∧ inDisc p z) →
      WordR main elemP (fun vs => vs = x :: Val.int S :: Val.int p :: Val.int b :: rest)
        (fun _ out => ∃ y, out = y :: Val.int S :: Val.int p :: Val.int b :: rest ∧
          (∃ z : ℤ × ℤ, x = cfxVal z ∧ y = Val.int (recov S p b z)) ∧ vsz y ≤ 2 * p + 8)
        (fun _ => Ke * (p + 1) * (p + 1)) := by
    rintro x ⟨z, rfl, hz⟩
    refine wordR_mono (helem main S p b z rest h2b hS hz) (fun _ h => h) ?_ ?_
    · rintro vs out hvs hout
      refine ⟨Val.int (recov S p b z), hout, ⟨z, rfl, rfl⟩, ?_⟩
      rw [Work.Main.vsz_int]
      exact le_trans (isz_recov_le h2b hS hz) (by omega)
    · intro vs hvs
      exact le_rfl
  have hxs : ∀ x ∈ zs.map cfxVal, (∃ z : ℤ × ℤ, x = cfxVal z ∧ inDisc p z) ∧ vsz x ≤ 2 * p + 8 := by
    intro x hx
    obtain ⟨z, hzx, rfl⟩ := List.mem_map.mp hx
    refine ⟨⟨z, rfl, hdisc.2 z hzx⟩, ?_⟩
    rw [Work.Main.vsz_cfxVal]
    have h1 := isz_fst_le (hdisc.2 z hzx)
    have h2 := isz_snd_le (hdisc.2 z hzx)
    omega
  have hmain := hmap main elemP (Val.int S :: Val.int p :: Val.int b :: rest)
      (fun x => ∃ z : ℤ × ℤ, x = cfxVal z ∧ inDisc p z)
      (fun x y => ∃ z : ℤ × ℤ, x = cfxVal z ∧ y = Val.int (recov S p b z))
      (Ke * (p + 1) * (p + 1)) (2 * p + 8) hper (zs.map cfxVal) hxs
  refine wordR_mono hmain ?_ ?_ ?_
  · intro vs hvs
    rw [hvs]; rfl
  · rintro vs out hvs ⟨ys, hout, hF2⟩
    obtain ⟨hs, hys, hlen, hget⟩ := extract_list hF2
    exact ⟨hs, hvs, by rw [hout, hys], hlen, hget⟩
  · intro vs hvs
    rw [List.length_map]
    exact costAux Ke Km zs.length p

end Work.Main.word
