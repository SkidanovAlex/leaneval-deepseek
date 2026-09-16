import Submission.CertEval

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-!
# The packed evaluation of the certificate's `I`-form, II: the sign combination

`Submission/CertEval.lean` reduces the `I`-form to the integer double sum
`certISum = Σ_{p,p'} Hc p p' · Ssum p.1 p'.1 50` grouped by signature, and proves
`Hc p p' = contMath p.2 p'.2 (|p.1|+|p'.1|)`.

Here we finish the *contraction*: `contMath v v' R` is the `a`-contraction of the coefficient
vectors `v`, `v'` against the kernel `Km`, and it is computed by the *packed* expression
`contPack v v' R` (four block extractions, one per sign pattern), so that the whole double sum
can be evaluated by a single base-`2^2048` convolution.

The mathematical content of `contMath_eq_contPack` is entirely elementary:
`v(a)v'(b) = (v⁺(a)-v⁻(a))(v'⁺(b)-v'⁻(b))`, expand, and read off each of the four ℕ-products
with the block-extraction lemma `blk_eq` of `CertEval.lean`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-! ## Splitting a `zip` membership -/

theorem mem_zip_fst {α β : Type*} {l₁ : List α} {l₂ : List β} {p : α × β}
    (h : p ∈ l₁.zip l₂) : p.1 ∈ l₁ := by
  induction l₁ generalizing l₂ with
  | nil => simp at h
  | cons c t ih =>
      cases l₂ with
      | nil => simp at h
      | cons d u =>
          rw [List.zip_cons_cons, List.mem_cons] at h
          rcases h with h | h
          · rw [h]; exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (ih h)

theorem mem_zip_snd {α β : Type*} {l₁ : List α} {l₂ : List β} {p : α × β}
    (h : p ∈ l₁.zip l₂) : p.2 ∈ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp at h
  | cons c t ih =>
      cases l₂ with
      | nil => simp at h
      | cons d u =>
          rw [List.zip_cons_cons, List.mem_cons] at h
          rcases h with h | h
          · rw [h]; exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (ih h)

theorem mem_cSigs_fst {p : List ℕ × List ℤ} (h : p ∈ cSigs) : p.1 ∈ certGroupSigs :=
  mem_zip_fst (by simpa only [cSigs] using h)

theorem mem_cSigs_snd {p : List ℕ × List ℤ} (h : p ∈ cSigs) : p.2 ∈ certGroupCoefs :=
  mem_zip_snd (by simpa only [cSigs] using h)

theorem map_zip_map_self {α β γ : Type*} (l : List α) (f : α → β) (g : α × β → γ) :
    ((l.zip (l.map f)).map g) = l.map (fun a => g (a, f a)) := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.map_cons, List.zip_cons_cons, List.map_cons, List.map_cons, ih]

/-! ## The global `decide`-checked facts about the certificate's grouped data -/

theorem certGroupSigs_sup_fact :
    certGroupSigs.all (fun σ => σ.all (fun a => (List.finRange 12).any
      (fun i => decide (a = 2 * ((i : ℕ) + 1))))) = true := by decide

theorem certGroupSigs_sum_fact :
    certGroupSigs.all (fun σ => decide (σ.sum ≤ 24)) = true := by decide

theorem certGroupCoefs_len_fact :
    certGroupCoefs.all (fun v => decide (v.length ≤ 26)) = true := by decide

theorem certGroupCoefs_abs_fact :
    certGroupCoefs.all (fun v => v.all (fun z => decide (z.natAbs ≤ 2 ^ 160))) = true := by decide

theorem certGroupSigs_support {σ : List ℕ} (h : σ ∈ certGroupSigs) :
    ∀ a ∈ σ, ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1) := by
  have h1 := List.all_eq_true.mp certGroupSigs_sup_fact σ h
  intro a ha
  obtain ⟨i, _, hi⟩ := List.any_eq_true.mp (List.all_eq_true.mp h1 a ha)
  exact ⟨i, of_decide_eq_true hi⟩

theorem certGroupSigs_sum_le {σ : List ℕ} (h : σ ∈ certGroupSigs) : σ.sum ≤ 24 :=
  of_decide_eq_true (List.all_eq_true.mp certGroupSigs_sum_fact σ h)

theorem certGroupCoefs_len {v : List ℤ} (h : v ∈ certGroupCoefs) : v.length ≤ 26 :=
  of_decide_eq_true (List.all_eq_true.mp certGroupCoefs_len_fact v h)

theorem certGroupCoefs_abs {v : List ℤ} (h : v ∈ certGroupCoefs) :
    ∀ z ∈ v, z.natAbs ≤ 2 ^ 160 := by
  have h1 := List.all_eq_true.mp certGroupCoefs_abs_fact v h
  intro z hz
  exact of_decide_eq_true (List.all_eq_true.mp h1 z hz)

/-! ## The bilinear expansion of a signed contraction -/

theorem sum_sub_mul_kernel (t : Finset ℕ) (u v : ℕ → ℤ) (K : ℕ → ℤ) :
    (∑ b ∈ t, (u b - v b) * K b) = (∑ b ∈ t, u b * K b) - (∑ b ∈ t, v b * K b) := by
  rw [Finset.sum_congr rfl (fun b _ => sub_mul (u b) (v b) (K b)), Finset.sum_sub_distrib]

/-- **The bilinear expansion of a signed double contraction.** -/
theorem contract_neg (s t : Finset ℕ) (K : ℕ → ℕ → ℤ) (f g f' g' : ℕ → ℤ) :
    (∑ a ∈ s, ∑ b ∈ t, (f a - g a) * (f' b - g' b) * K a b)
      = (∑ a ∈ s, ∑ b ∈ t, f a * f' b * K a b)
        - (∑ a ∈ s, ∑ b ∈ t, f a * g' b * K a b)
        - (∑ a ∈ s, ∑ b ∈ t, g a * f' b * K a b)
        + (∑ a ∈ s, ∑ b ∈ t, g a * g' b * K a b) := by
  have hstepA : ∀ a, (∑ b ∈ t, (f a - g a) * (f' b - g' b) * K a b)
      = (f a - g a) * ((∑ b ∈ t, f' b * K a b) - (∑ b ∈ t, g' b * K a b)) := by
    intro a
    rw [Finset.sum_congr rfl (fun b _ => mul_assoc (f a - g a) (f' b - g' b) (K a b)),
      ← Finset.mul_sum, sum_sub_mul_kernel]
  have hsplit4 : ∀ a, (f a - g a) *
        ((∑ b ∈ t, f' b * K a b) - (∑ b ∈ t, g' b * K a b))
      = (f a * (∑ b ∈ t, f' b * K a b) - f a * (∑ b ∈ t, g' b * K a b))
        - (g a * (∑ b ∈ t, f' b * K a b) - g a * (∑ b ∈ t, g' b * K a b)) :=
    fun a => by ring
  have hfour : ∀ (u w : ℕ → ℤ),
      (∑ a ∈ s, u a * (∑ b ∈ t, w b * K a b)) = (∑ a ∈ s, ∑ b ∈ t, u a * w b * K a b) := by
    intro u w
    rw [Finset.sum_congr rfl (fun a _ => Finset.mul_sum t (fun b => w b * K a b) (u a))]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => (mul_assoc _ _ _).symm))
  rw [Finset.sum_congr rfl (fun a _ => hstepA a)]
  rw [Finset.sum_congr rfl (fun a _ => hsplit4 a)]
  simp only [Finset.sum_sub_distrib]
  rw [hfour f f', hfour f g', hfour g f', hfour g g']
  ring

/-- Padding a sum over `range n` to `range m` when the summation is zero past `n`. -/
theorem sum_range_eq_of_zero {M : Type*} [AddCommMonoid M] {n m : ℕ} (hnm : n ≤ m)
    (f : ℕ → M) (hf : ∀ i, n ≤ i → f i = 0) :
    (∑ i ∈ Finset.range n, f i) = ∑ i ∈ Finset.range m, f i :=
  Finset.sum_subset (fun _ hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hnm))
    (fun i hi hni => hf i (by rw [Finset.mem_range] at hni; omega))

/-- `contMath` is unchanged by padding the two ranges to `26`. -/
theorem contMath_pad (v v' : List ℤ) (R : ℕ) (hv : v.length ≤ 26) (hv' : v'.length ≤ 26) :
    contMath v v' R = ∑ i ∈ Finset.range 26, ∑ j ∈ Finset.range 26,
        v.getD i 0 * v'.getD j 0 * (Km (i + j) R : ℤ) := by
  unfold contMath
  rw [sum_range_eq_of_zero hv (fun i => ∑ j ∈ Finset.range v'.length,
      v.getD i 0 * v'.getD j 0 * (Km (i + j) R : ℤ)) ?_]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    refine sum_range_eq_of_zero hv' (fun j => v.getD i 0 * v'.getD j 0 * (Km (i + j) R : ℤ))
      (fun j hj => by rw [List.getD_eq_default _ _ hj]; ring)
  · intro i hi
    refine Finset.sum_eq_zero (fun j _ => by
      rw [List.getD_eq_default _ _ hi]; ring)

theorem getD_vpos (v : List ℤ) (i : ℕ) : (vpos v).getD i 0 = ipos (v.getD i 0) := by
  rw [vpos]
  by_cases hi : i < v.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
      Option.map_some, Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some]
  · have hi' : v.length ≤ i := by omega
    rw [List.getD_eq_default (v.map ipos) 0 (by simpa using hi),
      List.getD_eq_default v 0 hi', ipos]
    simp

theorem getD_vneg (v : List ℤ) (i : ℕ) : (vneg v).getD i 0 = ineg (v.getD i 0) := by
  rw [vneg]
  by_cases hi : i < v.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
      Option.map_some, Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some]
  · have hi' : v.length ≤ i := by omega
    rw [List.getD_eq_default (v.map ineg) 0 (by simpa using hi),
      List.getD_eq_default v 0 hi', ineg]
    simp

/-- The positive and negative parts recombine to the integer. -/
theorem getD_eq_pos_sub_neg (v : List ℤ) (i : ℕ) :
    v.getD i 0 = ((vpos v).getD i 0 : ℤ) - ((vneg v).getD i 0 : ℤ) := by
  rw [getD_vpos, getD_vneg, ipos, ineg,
    Int.toNat_of_nonneg (le_max_right (v.getD i 0) 0),
    Int.toNat_of_nonneg (le_max_right (-(v.getD i 0)) 0)]
  exact Commons.Data.Int.int_eq_pos_sub_neg (v.getD i 0)

/-! ## The packed extraction in `ℤ` -/

/-- The block size bounds needed by the extraction, for a general kernel parameter `R`. -/
theorem blk_bounds_R (x y : ℕ → ℕ) (R : ℕ)
    (hx : (∑ i ∈ Finset.range 26, x i) ≤ 26 * 2 ^ 160)
    (hy : (∑ j ∈ Finset.range 26, y j) ≤ 26 * 2 ^ 160) :
    (∑ i ∈ Finset.range 26, x i) * (∑ j ∈ Finset.range 26, y j) < BP
      ∧ (∑ i ∈ Finset.range 26, x i) * (∑ j ∈ Finset.range 26, y j)
          * (∑ k ∈ Finset.range 51, Km (50 - k) R) < BP := by
  have hx0 : (0 : ℕ) ≤ ∑ i ∈ Finset.range 26, x i := Nat.zero_le _
  constructor
  · exact lt_of_le_of_lt (Nat.mul_le_mul hx hy) bound_ok1
  · exact lt_of_le_of_lt (Nat.mul_le_mul (Nat.mul_le_mul hx hy) (Kwz_le R)) bound_ok2

/-- **The block extraction, in `ℤ`.** -/
theorem blk_int (x y : ℕ → ℕ) (R : ℕ)
    (hxy : (∑ i ∈ Finset.range 26, x i) * (∑ j ∈ Finset.range 26, y j) < BP)
    (hxyz : (∑ i ∈ Finset.range 26, x i) * (∑ j ∈ Finset.range 26, y j)
              * (∑ k ∈ Finset.range 51, Km (50 - k) R) < BP) :
    ((blk (∑ i ∈ Finset.range 26, x i * BP ^ i)
        (∑ j ∈ Finset.range 26, y j * BP ^ j) R : ℕ) : ℤ)
      = ∑ i ∈ Finset.range 26, ∑ j ∈ Finset.range 26,
          (x i : ℤ) * (y j : ℤ) * (Km (i + j) R : ℤ) := by
  rw [blk_eq x y R hxy hxyz]
  simp only [Nat.cast_sum, Nat.cast_mul]

/-- **The four sign patterns of the extraction.** -/
theorem blk_int_pp (v v' : List ℤ) (R : ℕ) (hv : v.length ≤ 26) (hv' : v'.length ≤ 26)
    (hb : ∀ z ∈ v, z.natAbs ≤ 2 ^ 160) (hb' : ∀ z ∈ v', z.natAbs ≤ 2 ^ 160) :
    ((blk (pw (vpos v)) (pw (vpos v')) R : ℕ) : ℤ)
      = ∑ i ∈ Finset.range 26, ∑ j ∈ Finset.range 26,
          ((vpos v).getD i 0 : ℤ) * ((vpos v').getD j 0 : ℤ) * (Km (i + j) R : ℤ) := by
  rw [pwpos_le v hv, pwpos_le v' hv']
  have hbnds := blk_bounds_R (fun i => (vpos v).getD i 0) (fun j => (vpos v').getD j 0) R
    (sum_getD_le v hb).1 (sum_getD_le v' hb').1
  exact blk_int _ _ R hbnds.1 hbnds.2

theorem blk_int_pn (v v' : List ℤ) (R : ℕ) (hv : v.length ≤ 26) (hv' : v'.length ≤ 26)
    (hb : ∀ z ∈ v, z.natAbs ≤ 2 ^ 160) (hb' : ∀ z ∈ v', z.natAbs ≤ 2 ^ 160) :
    ((blk (pw (vpos v)) (pw (vneg v')) R : ℕ) : ℤ)
      = ∑ i ∈ Finset.range 26, ∑ j ∈ Finset.range 26,
          ((vpos v).getD i 0 : ℤ) * ((vneg v').getD j 0 : ℤ) * (Km (i + j) R : ℤ) := by
  rw [pwpos_le v hv, pwneg_le v' hv']
  have hbnds := blk_bounds_R (fun i => (vpos v).getD i 0) (fun j => (vneg v').getD j 0) R
    (sum_getD_le v hb).1 (sum_getD_le v' hb').2
  exact blk_int _ _ R hbnds.1 hbnds.2

theorem blk_int_np (v v' : List ℤ) (R : ℕ) (hv : v.length ≤ 26) (hv' : v'.length ≤ 26)
    (hb : ∀ z ∈ v, z.natAbs ≤ 2 ^ 160) (hb' : ∀ z ∈ v', z.natAbs ≤ 2 ^ 160) :
    ((blk (pw (vneg v)) (pw (vpos v')) R : ℕ) : ℤ)
      = ∑ i ∈ Finset.range 26, ∑ j ∈ Finset.range 26,
          ((vneg v).getD i 0 : ℤ) * ((vpos v').getD j 0 : ℤ) * (Km (i + j) R : ℤ) := by
  rw [pwneg_le v hv, pwpos_le v' hv']
  have hbnds := blk_bounds_R (fun i => (vneg v).getD i 0) (fun j => (vpos v').getD j 0) R
    (sum_getD_le v hb).2 (sum_getD_le v' hb').1
  exact blk_int _ _ R hbnds.1 hbnds.2

theorem blk_int_nn (v v' : List ℤ) (R : ℕ) (hv : v.length ≤ 26) (hv' : v'.length ≤ 26)
    (hb : ∀ z ∈ v, z.natAbs ≤ 2 ^ 160) (hb' : ∀ z ∈ v', z.natAbs ≤ 2 ^ 160) :
    ((blk (pw (vneg v)) (pw (vneg v')) R : ℕ) : ℤ)
      = ∑ i ∈ Finset.range 26, ∑ j ∈ Finset.range 26,
          ((vneg v).getD i 0 : ℤ) * ((vneg v').getD j 0 : ℤ) * (Km (i + j) R : ℤ) := by
  rw [pwneg_le v hv, pwneg_le v' hv']
  have hbnds := blk_bounds_R (fun i => (vneg v).getD i 0) (fun j => (vneg v').getD j 0) R
    (sum_getD_le v hb).2 (sum_getD_le v' hb').2
  exact blk_int _ _ R hbnds.1 hbnds.2

/-- The packed contraction of two coefficient vectors. -/
def contPack (v v' : List ℤ) (R : ℕ) : ℤ :=
  ((blk (pw (vpos v)) (pw (vpos v')) R : ℕ) : ℤ)
    - ((blk (pw (vpos v)) (pw (vneg v')) R : ℕ) : ℤ)
    - ((blk (pw (vneg v)) (pw (vpos v')) R : ℕ) : ℤ)
    + ((blk (pw (vneg v)) (pw (vneg v')) R : ℕ) : ℤ)

/-- **The contraction identity**: the packed sign combination computes the -contraction of
the two coefficient vectors against the kernel. -/
theorem contMath_eq_contPack (v v' : List ℤ) (R : ℕ) (hv : v.length ≤ 26) (hv' : v'.length ≤ 26)
    (hb : ∀ z ∈ v, z.natAbs ≤ 2 ^ 160) (hb' : ∀ z ∈ v', z.natAbs ≤ 2 ^ 160) :
    contMath v v' R = contPack v v' R := by
  rw [contMath_pad v v' R hv hv']
  unfold contPack
  rw [blk_int_pp v v' R hv hv' hb hb', blk_int_pn v v' R hv hv' hb hb',
    blk_int_np v v' R hv hv' hb hb', blk_int_nn v v' R hv hv' hb hb']
  have hget : ∀ i, v.getD i 0 = ((vpos v).getD i 0 : ℤ) - ((vneg v).getD i 0 : ℤ) :=
    fun i => getD_eq_pos_sub_neg v i
  have hget' : ∀ j, v'.getD j 0 = ((vpos v').getD j 0 : ℤ) - ((vneg v').getD j 0 : ℤ) :=
    fun j => getD_eq_pos_sub_neg v' j
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
    rw [hget i, hget' j]))]
  exact contract_neg (Finset.range 26) (Finset.range 26) (fun a b => (Km (a + b) R : ℤ))
    (fun a => ((vpos v).getD a 0 : ℤ)) (fun a => ((vneg v).getD a 0 : ℤ))
    (fun b => ((vpos v').getD b 0 : ℤ)) (fun b => ((vneg v').getD b 0 : ℤ))

end Commons.NumberTheory.MaynardSieve
