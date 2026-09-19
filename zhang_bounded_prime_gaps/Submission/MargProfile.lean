import Mathlib
import Submission.CertAnalytic
import Submission.M4Cert
import Submission.Commons.Combinatorics.Embedding.sum_preimage_expOf_smul
import Submission.CertSmoothJ

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

open MeasureTheory Finset
open scoped BigOperators

namespace Commons.NumberTheory.MaynardSieve

noncomputable section

/-! ## `lmono = θ · mfun` -/

/-- **The labelled monomial sum is `θ_α` times the monomial symmetric polynomial.** -/
theorem lmono_eq_theta_mul_mfun (α : List ℕ) (hα : 0 ∉ α) (k : ℕ) (t : Fin k → ℝ) :
    lmono α k t = (theta α : ℝ) * mfun α k t := by
  have h1 : (∑ e : Fin α.length ↪ Fin k, ∏ i : Fin α.length, (t (e i)) ^ (α.get i))
      = ∑ e : Fin α.length ↪ Fin k, ∏ c : Fin k, (t c) ^ (expOf α k e c) :=
    Finset.sum_congr rfl (fun e _ => prod_pow_expOf α k e t)
  have hmain : (∑ f ∈ Fintype.piFinset (fun _ : Fin k => Finset.range (α.sum + 1)),
      (if IsProfile α f then (∏ c : Fin k, (t c) ^ (f c)) else 0))
      = mfun α k t := by
    rw [mfun]
    rw [← Finset.sum_filter (s := Fintype.piFinset (fun _ : Fin k => Finset.range (α.sum + 1)))
      (p := IsProfile α) (f := fun f => ∏ c : Fin k, (t c) ^ (f c))]
  have h := Commons.Combinatorics.Embedding.sum_preimage_expOf_smul (k := k) α hα
    (M := ℝ) (fun f : Fin k → ℕ => ∏ c : Fin k, (t c) ^ (f c))
  calc lmono α k t
      = ∑ e : Fin α.length ↪ Fin k, ∏ i : Fin α.length, (t (e i)) ^ (α.get i) := rfl
    _ = ∑ e : Fin α.length ↪ Fin k, ∏ c : Fin k, (t c) ^ (expOf α k e c) := h1
    _ = (∏ v ∈ α.toFinset, (α.count v).factorial) •
          ∑ f ∈ Fintype.piFinset (fun _ : Fin k => Finset.range (α.sum + 1)),
            (if IsProfile α f then (∏ c : Fin k, (t c) ^ (f c)) else 0) := h
    _ = (theta α : ℝ) * mfun α k t := by rw [hmain, theta, nsmul_eq_mul]

/-! ## Profiles on an arbitrary finite index type -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `IsProf α f`: `f` is a profile of the multiset `α` on the index type `ι`. -/
def IsProf (α : List ℕ) (f : ι → ℕ) : Prop :=
  (∀ v ∈ α.toFinset, (Finset.univ.filter (fun c : ι => f c = v)).card = α.count v) ∧
    (∀ c : ι, f c = 0 ∨ f c ∈ α)

instance (α : List ℕ) : DecidablePred (IsProf (ι := ι) α) :=
  fun f => inferInstanceAs (Decidable (_ ∧ _))

/-- The profiles of `α` on `ι` whose values are bounded by `N`. -/
def profSet (N : ℕ) (α : List ℕ) : Finset (ι → ℕ) :=
  (Fintype.piFinset (fun _ : ι => Finset.range (N + 1))).filter (IsProf α)

/-- The monomial symmetric polynomial of the signature `α` on the index type `ι`. -/
def mfunS (α : List ℕ) (t : ι → ℝ) : ℝ :=
  ∑ f ∈ profSet (α.sum) α, ∏ c, (t c) ^ (f c)

theorem mem_profSet {N : ℕ} {α : List ℕ} {f : ι → ℕ} :
    f ∈ profSet (ι := ι) N α ↔ (∀ c, f c ≤ N) ∧ IsProf α f := by
  rw [profSet, Finset.mem_filter, Fintype.mem_piFinset]
  simp only [Finset.mem_range]
  exact ⟨fun h => ⟨fun c => Nat.lt_succ_iff.mp (h.1 c), h.2⟩,
    fun h => ⟨fun c => Nat.lt_succ_of_le (h.1 c), h.2⟩⟩

/-- `mfunS` on `Fin k` is the monomial symmetric polynomial `mfun`. -/
theorem mfunS_eq_mfun (α : List ℕ) (k : ℕ) (t : Fin k → ℝ) :
    mfunS (ι := Fin k) α t = mfun α k t := by
  have h : (Fintype.piFinset (fun _ : Fin k => Finset.range (α.sum + 1))).filter (IsProf α)
      = (Fintype.piFinset (fun _ : Fin k => Finset.range (α.sum + 1))).filter (IsProfile α) :=
    Finset.filter_congr (fun f _ => Iff.rfl)
  rw [mfunS, profSet, mfun, h]

theorem profSet_mono {M N : ℕ} {α : List ℕ} (hMN : M ≤ N) :
    profSet (ι := ι) M α ⊆ profSet N α := fun f hf => by
  rw [mem_profSet] at hf ⊢
  exact ⟨fun c => le_trans (hf.1 c) hMN, hf.2⟩

theorem profSet_range {M N : ℕ} {α : List ℕ} (hM : α.sum ≤ M) (hMN : M ≤ N) :
    profSet (ι := ι) N α = profSet M α := by
  refine Finset.Subset.antisymm (fun f hf => ?_) (profSet_mono hMN)
  rw [mem_profSet] at hf ⊢
  refine ⟨fun c => ?_, hf.2⟩
  rcases hf.2.2 c with h0 | hmem
  · rw [h0]; exact Nat.zero_le _
  · exact le_trans (List.le_sum_of_mem hmem) hM

/-! ## Reindexing -/

private theorem card_filter_comp_equiv {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (e : ι ≃ ι')
    (f : ι → ℕ) (v : ℕ) :
    (Finset.univ.filter (fun c' : ι' => f (e.symm c') = v)).card
      = (Finset.univ.filter (fun c : ι => f c = v)).card := by
  have hset : (Finset.univ.filter (fun c' : ι' => f (e.symm c') = v))
      = (Finset.univ.filter (fun c : ι => f c = v)).image e := by
    ext c'
    constructor
    · intro h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact Finset.mem_image.mpr ⟨e.symm c', Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩,
        Equiv.apply_symm_apply e c'⟩
    · intro h
      obtain ⟨c, hc, hcc⟩ := Finset.mem_image.mp h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      rw [← hcc, Equiv.symm_apply_apply]
      exact hc
  rw [hset, Finset.card_image_of_injective _ e.injective]

private theorem prod_comp_equiv {ι' : Type*} [Fintype ι'] (e : ι ≃ ι')
    (f : ι → ℕ) (t : ι' → ℝ) :
    (∏ c : ι, (t (e c)) ^ (f c)) = ∏ c' : ι', (t c') ^ (f (e.symm c')) := by
  refine Finset.prod_bij (fun c _ => e c) (fun c _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro c _ c' _ h; exact e.injective h
  · intro c' _; exact ⟨e.symm c', Finset.mem_univ _, by simp⟩
  · intro c _; simp

theorem mem_profSet_comp_equiv {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    (e : ι ≃ ι') (N : ℕ) (α : List ℕ) (f : ι → ℕ) :
    f ∈ profSet (ι := ι) N α ↔ (fun c' => f (e.symm c')) ∈ profSet (ι := ι') N α := by
  rw [mem_profSet, mem_profSet]
  constructor
  · rintro ⟨hbox, h1, h2⟩
    exact ⟨fun c' => hbox (e.symm c'), fun v hv => by
        rw [card_filter_comp_equiv e f v]; exact h1 v hv, fun c' => h2 (e.symm c')⟩
  · rintro ⟨hbox, h1, h2⟩
    refine ⟨fun c => by simpa using hbox (e c), fun v hv => ?_, fun c => by simpa using h2 (e c)⟩
    rw [← card_filter_comp_equiv e f v]
    exact h1 v hv

/-- **`mfunS` is invariant under reindexing the coordinates along an equivalence.** -/
theorem mfunS_comp_equiv {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (e : ι ≃ ι')
    (α : List ℕ) (t : ι' → ℝ) :
    mfunS (ι := ι) α (fun c => t (e c)) = mfunS (ι := ι') α t := by
  rw [mfunS, mfunS]
  refine Finset.sum_bij (fun f _ => fun c' => f (e.symm c')) ?_ ?_ ?_ ?_
  · intro f hf
    exact (mem_profSet_comp_equiv e α.sum α f).mp hf
  · intro f₁ hf₁ f₂ hf₂ h
    funext c
    have hc := congrFun h (e c)
    simpa using hc
  · intro g hg
    refine ⟨fun c => g (e c), ?_, ?_⟩
    · exact (mem_profSet_comp_equiv e α.sum α (fun c => g (e c))).mpr (by simpa using hg)
    · funext c'
      simp
  · intro f hf
    exact prod_comp_equiv e f t


/-! ## Splitting a profile at a coordinate -/

section Decomp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Reindexing a sum over the complement of `i`. -/
theorem sum_subtype_ne {β : Type*} [AddCommMonoid β] (i : ι) (F : ι → β) :
    (∑ c : {c : ι // c ≠ i}, F c.1) = ∑ c ∈ (Finset.univ.erase i), F c :=
  (Finset.sum_subtype (p := fun c => c ≠ i) (Finset.univ.erase i)
    (fun x => by simp [Finset.mem_erase]) F).symm

/-- Reindexing a product over the complement of `i`. -/
theorem prod_subtype_ne {β : Type*} [CommMonoid β] (i : ι) (F : ι → β) :
    (∏ c : {c : ι // c ≠ i}, F c.1) = ∏ c ∈ (Finset.univ.erase i), F c :=
  (Finset.prod_subtype (p := fun c => c ≠ i) (Finset.univ.erase i)
    (fun x => by simp [Finset.mem_erase]) F).symm

/-- The "clean" characterization of the profile condition. -/
theorem isProf_iff (α : List ℕ) (hα : 0 ∉ α) (f : ι → ℕ) :
    IsProf (ι := ι) α f ↔
      ∀ v : ℕ, v ≠ 0 → (Finset.univ.filter (fun c : ι => f c = v)).card = α.count v := by
  constructor
  · rintro ⟨h1, h2⟩ v hv
    by_cases hv' : v ∈ α.toFinset
    · exact h1 v hv'
    · have hcnt : α.count v = 0 := by
        rw [List.count_eq_zero]
        intro hmem
        exact hv' (List.mem_toFinset.mpr hmem)
      have hzero : (Finset.univ.filter (fun c : ι => f c = v)).card = 0 := by
        rw [Finset.card_eq_zero]
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]
        intro hc
        rcases h2 c with h0 | hmem
        · exact hv (hc ▸ h0)
        · exact hv' (List.mem_toFinset.mpr (hc ▸ hmem))
      rw [hzero, hcnt]
  · intro h
    refine ⟨fun v hv => h v ?_, fun c => ?_⟩
    · intro h0
      exact hα (List.mem_toFinset.mp (h0 ▸ hv))
    · by_contra hc
      rw [not_or] at hc
      obtain ⟨hc1, hc2⟩ := hc
      have h3 := h (f c) hc1
      rw [List.count_eq_zero.mpr hc2] at h3
      have h4 : 0 < (Finset.univ.filter (fun c' : ι => f c' = f c)).card :=
        Finset.card_pos.mpr ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, rfl⟩⟩
      exact absurd (h3 ▸ h4) (Nat.lt_irrefl 0)

/-- Insert the value `p` at the coordinate `i` of a function on the complement of `i`. -/
def insFun (i : ι) (p : ℕ) (g : {c : ι // c ≠ i} → ℕ) : ι → ℕ :=
  fun c => if h : c = i then p else g ⟨c, h⟩

theorem insFun_self (i : ι) (p : ℕ) (g : {c : ι // c ≠ i} → ℕ) : insFun i p g i = p :=
  dif_pos rfl

theorem insFun_of_ne (i : ι) (p : ℕ) (g : {c : ι // c ≠ i} → ℕ) {c : ι} (hc : c ≠ i) :
    insFun i p g c = g ⟨c, hc⟩ := dif_neg hc

theorem insFun_injective (i : ι) (p : ℕ) : Function.Injective (insFun (ι := ι) i p) := by
  intro g₁ g₂ h
  funext c
  have hc := congrFun h c.1
  rwa [insFun_of_ne i p g₁ c.2, insFun_of_ne i p g₂ c.2] at hc

/-- **The value count splits at a coordinate.** -/
theorem card_filter_eq_subtype_add (i : ι) (f : ι → ℕ) (v : ℕ) :
    (Finset.univ.filter (fun c : ι => f c = v)).card
      = (Finset.univ.filter (fun c : {c : ι // c ≠ i} => f c.1 = v)).card
        + (if f i = v then 1 else 0) := by
  have hcard1 : (Finset.univ.filter (fun c : {c : ι // c ≠ i} => f c.1 = v)).card
      = (Finset.univ.filter (fun c : ι => f c = v ∧ c ≠ i)).card := by
    have h1 : (Finset.univ.filter (fun c : {c : ι // c ≠ i} => f c.1 = v)).card
        = ((Finset.univ.erase i).filter (fun c : ι => f c = v)).card := by
      rw [Finset.card_filter, Finset.card_filter,
        sum_subtype_ne i (fun c : ι => if f c = v then (1:ℕ) else 0)]
    rw [h1]
    congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
    tauto
  have hsplit : (Finset.univ.filter (fun c : ι => f c = v))
      = (Finset.univ.filter (fun c : ι => f c = v ∧ c ≠ i))
        ∪ (Finset.univ.filter (fun c : ι => f c = v ∧ c = i)) := by
    ext c
    by_cases h : c = i <;> simp [h]
  have hdisj : Disjoint (Finset.univ.filter (fun c : ι => f c = v ∧ c ≠ i))
      (Finset.univ.filter (fun c : ι => f c = v ∧ c = i)) := by
    rw [Finset.disjoint_left]
    intro c h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact h1.2 h2.2
  have hcard2 : (Finset.univ.filter (fun c : ι => f c = v ∧ c = i)).card
      = if f i = v then 1 else 0 := by
    by_cases hv : f i = v
    · rw [if_pos hv]
      have hsingle : (Finset.univ.filter (fun c : ι => f c = v ∧ c = i)) = {i} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hv, h⟩⟩
      rw [hsingle, Finset.card_singleton]
    · rw [if_neg hv]
      refine Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr (fun c hc => ?_))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      exact hv (by rw [← hc.2]; exact hc.1)
  rw [hcard1, hsplit, Finset.card_union_of_disjoint hdisj, hcard2]

/-- Restricting a profile to the complement of a coordinate. -/
theorem isProf_fiber {α : List ℕ} (hα : 0 ∉ α) {f : ι → ℕ} (hf : IsProf α f) (i : ι) :
    IsProf (eraseOne α (f i)) (fun c : {c : ι // c ≠ i} => f c.1) := by
  have hfi : f i = 0 ∨ f i ∈ α := hf.2 i
  rw [isProf_iff _ hα] at hf
  rw [isProf_iff _ (eraseOne_notMem_zero α hα (f i))]
  intro v hv
  have hcount : α.count v
      = (eraseOne α (f i)).count v + (if v = f i then 1 else 0) := by
    rcases hfi with h0 | hmem
    · rw [h0, eraseOne_eq_self_of_notMem α 0 hα, if_neg (fun h : v = 0 => hv h), add_zero]
    · exact count_eraseOne α (f i) v hmem
  have h1 := hf v hv
  have h2 := card_filter_eq_subtype_add (ι := ι) i f v
  have hif : (if f i = v then (1:ℕ) else 0) = (if v = f i then 1 else 0) := by
    by_cases h : v = f i
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  rw [hif] at h2
  rcases eq_or_ne v (f i) with hv' | hv'
  · rw [if_pos hv'] at h2 hcount
    omega
  · rw [if_neg hv'] at h2 hcount
    omega

/-- Inserting a value at a coordinate to obtain a profile of `α`. -/
theorem isProf_insFun {α : List ℕ} (hα : 0 ∉ α) (i : ι) (p : ℕ)
    (hp : p = 0 ∨ p ∈ α) {g : {c : ι // c ≠ i} → ℕ}
    (hg : IsProf (eraseOne α p) g) : IsProf α (insFun i p g) := by
  rw [isProf_iff _ hα]
  intro v hv
  have hcount : α.count v
      = (eraseOne α p).count v + (if v = p then 1 else 0) := by
    rcases hp with h0 | hmem
    · rw [h0, eraseOne_eq_self_of_notMem α 0 hα, if_neg (fun h : v = 0 => hv h), add_zero]
    · exact count_eraseOne α p v hmem
  have hg' := (isProf_iff _ (eraseOne_notMem_zero α hα p) g).mp hg v hv
  have h2 := card_filter_eq_subtype_add (ι := ι) i (insFun i p g) v
  have hsub : (Finset.univ.filter (fun c : {c : ι // c ≠ i} => insFun i p g c.1 = v)).card
      = (Finset.univ.filter (fun c : {c : ι // c ≠ i} => g c = v)).card := by
    congr 1
    refine Finset.filter_congr (fun c _ => ?_)
    rw [insFun_of_ne i p g c.2]
  rw [hsub, insFun_self i p g] at h2
  have hif : (if p = v then (1:ℕ) else 0) = (if v = p then 1 else 0) := by
    by_cases h : v = p
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  rw [hif] at h2
  rcases eq_or_ne v p with hv' | hv'
  · rw [if_pos hv'] at h2 hcount
    omega
  · rw [if_neg hv'] at h2 hcount
    omega

end Decomp


/-! ## The marginal decomposition of the monomial symmetric polynomial -/

/-- A profile of `α` has all its values at most `α.sum`. -/
theorem le_sum_of_isProf {α : List ℕ} {f : ι → ℕ} (hf : IsProf α f) (c : ι) :
    f c ≤ α.sum := by
  rcases hf.2 c with h0 | hmem
  · rw [h0]; exact Nat.zero_le _
  · exact List.le_sum_of_mem hmem

/-- **The marginal decomposition.**

The monomial symmetric polynomial of `α`, evaluated after inserting the value `x` at the
coordinate `i` and the values `t` on the complement, is the sum over the parts `v` of `α`
(and `v = 0`) of `x^v` times the monomial symmetric polynomial of `eraseOne α v` — with
coefficient `1`, the symmetric normalisation of Polymath8a §7.2. -/
theorem mfunS_decomp (α : List ℕ) (hα : 0 ∉ α) (i : ι) (x : ℝ) (t : ι → ℝ) :
    mfunS α (fun c => if c = i then x else t c)
      = ∑ v ∈ (0 :: α.dedup).toFinset,
          x ^ v * mfunS (eraseOne α v) (fun c : {c : ι // c ≠ i} => t c.1) := by
  have hprod : ∀ f : ι → ℕ, (∏ c, (if c = i then x else t c) ^ (f c))
      = x ^ (f i) * ∏ c : {c : ι // c ≠ i}, (t c.1) ^ (f c.1) := by
    intro f
    rw [← Finset.mul_prod_erase (Finset.univ)
      (fun c : ι => (if c = i then x else t c) ^ (f c)) (Finset.mem_univ i), if_pos rfl]
    congr 1
    rw [prod_subtype_ne i (fun c : ι => (t c) ^ (f c))]
    refine Finset.prod_congr rfl (fun c hc => ?_)
    rw [Finset.mem_erase] at hc
    rw [if_neg hc.1]
  have hmem : ∀ f ∈ profSet (ι := ι) (α.sum) α, f i ∈ (0 :: α.dedup).toFinset := by
    intro f hf
    rw [mem_profSet] at hf
    rw [List.mem_toFinset, List.mem_cons]
    rcases hf.2.2 i with h0 | hmem
    · exact Or.inl h0
    · exact Or.inr (List.mem_dedup.mpr hmem)
  conv_lhs => rw [mfunS]
  rw [Finset.sum_congr rfl (fun f _ => hprod f)]
  rw [← Finset.sum_fiberwise_of_maps_to hmem (fun f : ι → ℕ =>
    x ^ (f i) * ∏ c : {c : ι // c ≠ i}, (t c.1) ^ (f c.1))]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  have hvle : v ≤ α.sum := by
    rw [List.mem_toFinset, List.mem_cons] at hv
    rcases hv with h0 | hmem
    · rw [h0]; exact Nat.zero_le _
    · exact List.le_sum_of_mem (List.mem_dedup.mp hmem)
  rw [show (∑ f ∈ (profSet (ι := ι) (α.sum) α).filter (fun f => f i = v),
        x ^ (f i) * ∏ c : {c : ι // c ≠ i}, (t c.1) ^ (f c.1))
      = ∑ f ∈ (profSet (ι := ι) (α.sum) α).filter (fun f => f i = v),
        x ^ v * ∏ c : {c : ι // c ≠ i}, (t c.1) ^ (f c.1) from
      Finset.sum_congr rfl (fun f hf => by
        rw [Finset.mem_filter] at hf
        rw [hf.2])]
  conv_rhs => rw [mfunS, Finset.mul_sum]
  refine Finset.sum_bij (fun f _ => fun c : {c : ι // c ≠ i} => f c.1) ?_ ?_ ?_ ?_
  · intro f hf
    rw [Finset.mem_filter, mem_profSet] at hf
    obtain ⟨hf1, hfi⟩ := hf
    rw [mem_profSet]
    have hprof : IsProf (eraseOne α v) (fun c : {c : ι // c ≠ i} => f c.1) := by
      have := isProf_fiber hα hf1.2 i
      rwa [hfi] at this
    exact ⟨fun c => le_sum_of_isProf hprof c, hprof⟩
  · intro f₁ hf₁ f₂ hf₂ h
    rw [Finset.mem_filter] at hf₁ hf₂
    funext c
    by_cases hc : c = i
    · rw [hc, hf₁.2, hf₂.2]
    · have := congrFun h ⟨c, hc⟩
      simpa [insFun_of_ne] using this
  · intro g hg
    refine ⟨insFun i v g, ?_, ?_⟩
    · rw [Finset.mem_filter, mem_profSet]
      rw [mem_profSet] at hg
      refine ⟨⟨fun c => ?_, isProf_insFun hα i v ?_ hg.2⟩, insFun_self i v g⟩
      · by_cases hc : c = i
        · rw [hc, insFun_self]; exact hvle
        · rw [insFun_of_ne i v g hc]
          exact le_trans (hg.1 ⟨c, hc⟩) (eraseOne_sum_le α v)
      · rw [List.mem_toFinset, List.mem_cons] at hv
        rcases hv with h0 | hmem
        · exact Or.inl h0
        · exact Or.inr (List.mem_dedup.mp hmem)
    · funext c
      exact insFun_of_ne i v g c.2
  · intro f hf
    rfl



/-! ## The decomposition along a line `insAt` -/

/-- **The marginal decomposition of the monomial symmetric polynomial.**

Evaluating `m_α` after inserting the value `x` in the coordinate `i` of the point `u` gives the
sum over the parts `v` of `α` (and `v = 0`) of `x^v · m_{α - v}(u)`. -/
theorem mfun_insAt {k : ℕ} (α : List ℕ) (hα : 0 ∉ α) (i : Fin (k+1)) (x : ℝ)
    (u : Fin k → ℝ) :
    mfun α (k+1) (insAt i x u)
      = ∑ v ∈ (0 :: α.dedup).toFinset, x ^ v * mfun (eraseOne α v) k u := by
  classical
  set t : Fin (k+1) → ℝ := fun c => if h : c ≠ i then u ((finSuccAboveEquiv i).symm ⟨c, h⟩)
    else 0 with ht
  have ht_apply : ∀ c : Fin (k+1), t c
      = if h : c ≠ i then u ((finSuccAboveEquiv i).symm ⟨c, h⟩) else 0 := fun c => rfl
  have hins : insAt i x u = fun c => if c = i then x else t c := by
    funext c
    rw [insAt]
    by_cases h : c = i
    · rw [dif_pos h, if_pos h]
    · rw [dif_neg h, if_neg h]
      rw [ht_apply, dif_pos h]
  have hmarg : (fun c : {c : Fin (k+1) // c ≠ i} => t c.1)
      = fun c : {c : Fin (k+1) // c ≠ i} => u ((finSuccAboveEquiv i).symm c) := by
    funext c
    rw [ht_apply, dif_pos c.2]
  have hcomp : (fun c : Fin k => t (finSuccAboveEquiv i c)) = u := by
    funext c
    have hne : ((finSuccAboveEquiv i c : {c : Fin (k+1) // c ≠ i}) : Fin (k+1)) ≠ i :=
      (finSuccAboveEquiv i c).2
    rw [ht_apply, dif_pos hne]
    have hsub : (⟨↑((finSuccAboveEquiv i) c), hne⟩ : {c : Fin (k+1) // c ≠ i})
        = finSuccAboveEquiv i c := Subtype.ext rfl
    rw [hsub, Equiv.symm_apply_apply]
  rw [← mfunS_eq_mfun (α := α) (k := k+1) (t := insAt i x u), hins,
    mfunS_decomp α hα i x t]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  congr 1
  rw [← mfunS_eq_mfun (α := eraseOne α v) (k := k), hmarg,
    mfunS_comp_equiv (finSuccAboveEquiv i).symm (eraseOne α v) u]


/-! ## The labelled marginal decomposition -/

/-- Multiplying `θ` by the multiplicity factor of a deleted part. -/
theorem theta_eq_count_mul_eraseOne {α : List ℕ} {v : ℕ} (hv : v ∈ α) :
    theta α = α.count v * theta (eraseOne α v) := by
  have hcnt : ∀ u, α.count u = (eraseOne α v).count u + (if u = v then 1 else 0) :=
    fun u => count_eraseOne α v u hv
  have hcv : (eraseOne α v).count v + 1 = α.count v := by
    have h := hcnt v
    rw [if_pos rfl] at h
    omega
  have hsplitR : (∏ u ∈ α.toFinset, ((eraseOne α v).count u).factorial)
      = ((eraseOne α v).count v).factorial
        * ∏ u ∈ α.toFinset.erase v, ((eraseOne α v).count u).factorial :=
    (Finset.mul_prod_erase _ _ (List.mem_toFinset.mpr hv)).symm
  have hsplitL : (∏ u ∈ α.toFinset, (α.count u).factorial)
      = (α.count v).factorial * ∏ u ∈ α.toFinset.erase v, (α.count u).factorial :=
    (Finset.mul_prod_erase _ _ (List.mem_toFinset.mpr hv)).symm
  have hprod : (∏ u ∈ α.toFinset, ((eraseOne α v).count u).factorial)
      = ∏ u ∈ α.toFinset, ((eraseOne α v).count u).factorial := rfl
  have hperm : (∏ u ∈ α.toFinset, ((eraseOne α v).count u).factorial)
      = ∏ u ∈ (eraseOne α v).toFinset, ((eraseOne α v).count u).factorial := by
    refine (Finset.prod_subset ?_ ?_).symm
    · intro x hx
      rw [List.mem_toFinset] at hx ⊢
      have h := hcnt x
      have hpos : 0 < List.count x (eraseOne α v) := List.count_pos_iff.mpr hx
      have : 0 < List.count x α := by omega
      exact List.count_pos_iff.mp this
    · intro x _ hx
      have hx0 : List.count x (eraseOne α v) = 0 :=
        List.count_eq_zero.mpr (fun hx' => hx (List.mem_toFinset.mpr hx'))
      rw [hx0, Nat.factorial_zero]
  have hfac : (α.count v).factorial
      = α.count v * ((eraseOne α v).count v).factorial := by
    rw [← hcv, Nat.factorial_succ]
  have heq : (∏ u ∈ α.toFinset.erase v, (α.count u).factorial)
      = ∏ u ∈ α.toFinset.erase v, ((eraseOne α v).count u).factorial := by
    refine Finset.prod_congr rfl (fun u hu => ?_)
    rw [Finset.mem_erase] at hu
    rw [hcnt u, if_neg hu.1, add_zero]
  rw [theta, theta, ← hperm, hsplitR, hsplitL, hfac, heq]
  ring

/-- The multiplicity factor attached to a deleted part. -/
theorem theta_mul_factor {α : List ℕ} (hα : 0 ∉ α) {v : ℕ}
    (hv : v ∈ (0 :: α.dedup).toFinset) :
    (theta α : ℝ)
      = (if v = 0 then (1:ℝ) else (α.count v : ℝ)) * (theta (eraseOne α v) : ℝ) := by
  rw [List.mem_toFinset, List.mem_cons] at hv
  rcases hv with h0 | hmem
  · rw [h0, eraseOne_eq_self_of_notMem α 0 hα, if_pos rfl, one_mul]
  · rw [if_neg (fun h : v = 0 => hα (h ▸ List.mem_dedup.mp hmem))]
    exact_mod_cast theta_eq_count_mul_eraseOne (List.mem_dedup.mp hmem)

/-- **The marginal decomposition of the labelled monomial sum.** -/
theorem lmono_insAt {k : ℕ} (α : List ℕ) (hα : 0 ∉ α) (i : Fin (k+1)) (x : ℝ)
    (u : Fin k → ℝ) :
    lmono α (k+1) (insAt i x u)
      = ∑ v ∈ (0 :: α.dedup).toFinset,
          (if v = 0 then 1 else (α.count v : ℝ)) * (x ^ v * lmono (eraseOne α v) k u) := by
  rw [lmono_eq_theta_mul_mfun α hα, mfun_insAt α hα i x u, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  rw [lmono_eq_theta_mul_mfun (eraseOne α v) (eraseOne_notMem_zero α hα v) k u,
    theta_mul_factor hα hv]
  ring

end

end Commons.NumberTheory.MaynardSieve
