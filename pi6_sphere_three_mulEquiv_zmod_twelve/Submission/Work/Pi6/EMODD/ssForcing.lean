import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.EMM2.SSKit
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

/-!
# Forcing lemmas for the multiplicative Serre spectral sequence over a field

This file proves `Work.Pi6.EMODD.ssForcing`: two "forcing" statements for the multiplicative
cohomological Serre spectral sequence over a field `𝕜` (the abstract spectral sequence
`Work.Pi6.CohSS`, whose convergence and edge maps are axiomatised by `Work.Pi6.IsSerreMSS`).

(A) If the fibre has trivial cohomology in positive degrees `≤ N` and the total space has trivial
cohomology in degrees `1 … N`, then the base has trivial cohomology in degrees `1 … N`.

(B) If fibre and total space have one-dimensional cohomology in every even degree `≤ N`, vanish in
odd degrees, are finite dimensional (the base as well), and the fibre classes survive in even
degrees, then the base has trivial cohomology in degrees `1 … N`.

The proof is pure bookkeeping on the axioms of `Work.Pi6.CohSS` plus the dimension count
`conv_dim` of `Work.Pi6.IsSerreMSS`.  The helpers are:

* `ssF_exists_ne_zero_iterate_of_dzero` — a nonzero class of `E_r^a` survives `t` pages provided
  nothing hits `a` on the pages `r ≤ k < r + t` (in the form "the incoming differential is zero",
  which is weaker than "the source module vanishes") and nothing leaves `a`;
* `ssF_d_col_eq_zero_of_survives` — a surviving class of `E_{s+1}^{0,q}` forces the differential
  `d_s^{0,q}` out of column `0` to vanish, when `dim E_2^{0,q} ≤ 1`;
* `ssF_finrank_Coh_zero` — `H^0(B)` is one-dimensional, from `conv_dim` in degree `0`.
-/

namespace Work.Pi6.EMODD

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

variable {𝕜 : Type} [Field 𝕜]

/-! ## Linear algebra over a field: `IsZero`, `Nontrivial`, tensor products -/

/-- A `𝕜`-module is zero iff it is a subsingleton type. -/
theorem ssF_not_isZero_iff_nontrivial (M : ModuleCat 𝕜) : ¬ IsZero M ↔ Nontrivial M := by
  constructor
  · intro h
    by_contra hnt
    haveI : Subsingleton (↥M) := ⟨fun x y => by
      by_contra hxy
      exact hnt ⟨x, y, hxy⟩⟩
    exact h (ModuleCat.isZero_of_subsingleton M)
  · rintro ⟨x, y, hxy⟩ hz
    haveI : Subsingleton (↥M) := ModuleCat.subsingleton_of_isZero hz
    exact hxy (Subsingleton.elim x y)

/-- A nonzero module has a nonzero element. -/
theorem ssF_exists_ne_zero_of_not_isZero {M : ModuleCat 𝕜} (h : ¬ IsZero M) :
    ∃ x : M, x ≠ 0 := by
  obtain ⟨x, y, hxy⟩ := (ssF_not_isZero_iff_nontrivial M).mp h
  exact ⟨x - y, sub_ne_zero.mpr hxy⟩

/-- A module with a nonzero element is not zero. -/
theorem ssF_not_isZero_of_exists_ne_zero {M : ModuleCat 𝕜} (h : ∃ x : M, x ≠ 0) :
    ¬ IsZero M := by
  rintro hz
  obtain ⟨x, hx⟩ := h
  exact hx ((ModuleCat.subsingleton_of_isZero hz).elim x 0)

/-- A finite-dimensional nonzero module has positive dimension. -/
theorem ssF_finrank_pos {M : ModuleCat 𝕜} (hfd : FiniteDimensional 𝕜 M) (hne : ¬ IsZero M) :
    0 < Module.finrank 𝕜 M := by
  haveI : Module.Finite 𝕜 (↥M) := hfd
  rw [Nat.pos_iff_ne_zero]
  intro h0
  rw [Module.finrank_eq_zero_iff_of_free] at h0
  haveI := h0
  exact hne (ModuleCat.isZero_of_subsingleton M)

/-- A tensor product is a subsingleton if its left factor is. -/
theorem ssF_subsingleton_tmul_left {M N : Type} [AddCommGroup M] [Module 𝕜 M] [AddCommGroup N]
    [Module 𝕜 N] [Subsingleton M] : Subsingleton (M ⊗[𝕜] N) := by
  have h0 : ∀ x : M ⊗[𝕜] N, x = 0 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul m n => rw [Subsingleton.elim m 0, TensorProduct.zero_tmul]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun a b => by rw [h0 a, h0 b]⟩

/-- A tensor product is a subsingleton if its right factor is. -/
theorem ssF_subsingleton_tmul_right {M N : Type} [AddCommGroup M] [Module 𝕜 M] [AddCommGroup N]
    [Module 𝕜 N] [Subsingleton N] : Subsingleton (M ⊗[𝕜] N) := by
  have h0 : ∀ x : M ⊗[𝕜] N, x = 0 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul m n => rw [Subsingleton.elim n 0, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun a b => by rw [h0 a, h0 b]⟩

/-- `IsZero` transfers backwards along an isomorphism. -/
theorem ssF_isZero_of_iso {M N : ModuleCat 𝕜} (e : M ≅ N) (h : IsZero M) : IsZero N := by
  haveI : Subsingleton (↥M) := ModuleCat.subsingleton_of_isZero h
  haveI : Subsingleton (↥N) := e.toLinearEquiv.symm.injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton N

/-- A module isomorphic to `𝕜` is nonzero. -/
theorem ssF_not_isZero_of_iso_k {M : ModuleCat 𝕜} (h : Nonempty (M ≅ ModuleCat.of 𝕜 𝕜)) :
    ¬ IsZero M := by
  obtain ⟨e⟩ := h
  intro hz
  haveI : Subsingleton (↥M) := ModuleCat.subsingleton_of_isZero hz
  haveI : Subsingleton (↥(ModuleCat.of 𝕜 𝕜)) := e.toLinearEquiv.symm.injective.subsingleton
  exact one_ne_zero (Subsingleton.elim (1 : 𝕜) 0)

/-- A module isomorphic to `𝕜` has dimension one. -/
theorem ssF_finrank_eq_one_of_iso_k {M : ModuleCat 𝕜}
    (h : Nonempty (M ≅ ModuleCat.of 𝕜 𝕜)) : Module.finrank 𝕜 M = 1 := by
  obtain ⟨e⟩ := h
  rw [LinearEquiv.finrank_eq e.toLinearEquiv]
  exact Module.finrank_self 𝕜

/-! ## The `E_2` page of a Serre spectral sequence -/

/-- The fibre of `p` over its base point. -/
abbrev ssF_Fib {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e₀ : E) :
    Type :=
  Work.StemsB.fibre p (p e₀)

/-- `E_2^{s,q}` vanishes if the base group `H^s(B)` does. -/
theorem ssF_e2_isZero_of_left {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (S : CohSS 𝕜) (p : C(E, B)) (e₀ : E) (N : ℕ) (hS : IsSerreMSS S p e₀ N) {s q : ℕ}
    (hs : s ≤ N) (hq : q ≤ N) (h : IsZero (Coh 𝕜 B s)) : IsZero (S.E 2 ((s : ℤ), (q : ℤ))) := by
  obtain ⟨e2, _⟩ := hS
  haveI : Subsingleton (↥(Coh 𝕜 B s)) := ModuleCat.subsingleton_of_isZero h
  haveI : Subsingleton (↥(Coh 𝕜 B s) ⊗[𝕜] ↥(Coh 𝕜 (ssF_Fib p e₀) q)) :=
    ssF_subsingleton_tmul_left
  exact ssF_isZero_of_iso (e2 s q hs hq).symm (ModuleCat.isZero_of_subsingleton _)

/-- `E_2^{s,q}` vanishes if the fibre group `H^q(F)` does. -/
theorem ssF_e2_isZero_of_right {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (S : CohSS 𝕜) (p : C(E, B)) (e₀ : E) (N : ℕ) (hS : IsSerreMSS S p e₀ N) {s q : ℕ}
    (hs : s ≤ N) (hq : q ≤ N) (h : IsZero (Coh 𝕜 (ssF_Fib p e₀) q)) :
    IsZero (S.E 2 ((s : ℤ), (q : ℤ))) := by
  obtain ⟨e2, _⟩ := hS
  haveI : Subsingleton (↥(Coh 𝕜 (ssF_Fib p e₀) q)) := ModuleCat.subsingleton_of_isZero h
  haveI : Subsingleton (↥(Coh 𝕜 B s) ⊗[𝕜] ↥(Coh 𝕜 (ssF_Fib p e₀) q)) :=
    ssF_subsingleton_tmul_right
  exact ssF_isZero_of_iso (e2 s q hs hq).symm (ModuleCat.isZero_of_subsingleton _)

/-- `E_2^{s,q}` is nonzero as soon as `H^s(B)` and `H^q(F)` are. -/
theorem ssF_e2_not_isZero {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (S : CohSS 𝕜) (p : C(E, B)) (e₀ : E) (N : ℕ) (hS : IsSerreMSS S p e₀ N) {s q : ℕ}
    (hs : s ≤ N) (hq : q ≤ N) (hB : ¬ IsZero (Coh 𝕜 B s))
    (hF : ¬ IsZero (Coh 𝕜 (ssF_Fib p e₀) q)) : ¬ IsZero (S.E 2 ((s : ℤ), (q : ℤ))) := by
  obtain ⟨e2, _⟩ := hS
  obtain ⟨b, hb⟩ := ssF_exists_ne_zero_of_not_isZero hB
  obtain ⟨f, hf⟩ := ssF_exists_ne_zero_of_not_isZero hF
  have ht : b ⊗ₜ[𝕜] f ≠ 0 := tmul_ne_zero_of_ne_zero hb hf
  intro hz
  haveI : Subsingleton (↥(S.E 2 ((s : ℤ), (q : ℤ)))) := ModuleCat.subsingleton_of_isZero hz
  haveI : Subsingleton (TensorProduct 𝕜 ↥(Coh 𝕜 B s) ↥(Coh 𝕜 (ssF_Fib p e₀) q)) :=
    (e2 s q hs hq).toLinearEquiv.symm.injective.subsingleton
  exact ht (Subsingleton.elim _ _)

/-- `dim E_2^{s,q} = dim H^s(B) · dim H^q(F)`. -/
theorem ssF_e2_finrank {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (S : CohSS 𝕜) (p : C(E, B)) (e₀ : E) (N : ℕ) (hS : IsSerreMSS S p e₀ N) {s q : ℕ}
    (hs : s ≤ N) (hq : q ≤ N) :
    Module.finrank 𝕜 (S.E 2 ((s : ℤ), (q : ℤ))) =
      Module.finrank 𝕜 (Coh 𝕜 B s) * Module.finrank 𝕜 (Coh 𝕜 (ssF_Fib p e₀) q) := by
  obtain ⟨e2, _⟩ := hS
  rw [LinearEquiv.finrank_eq (e2 s q hs hq).toLinearEquiv]
  rw [Module.finrank_tensorProduct]

/-- `E_2^{s,q}` is finite-dimensional if `H^s(B)` and `H^q(F)` are. -/
theorem ssF_finiteDimensional_E2 {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (S : CohSS 𝕜) (p : C(E, B)) (e₀ : E) (N : ℕ) (hS : IsSerreMSS S p e₀ N) {s q : ℕ}
    (hs : s ≤ N) (hq : q ≤ N) (hB : FiniteDimensional 𝕜 (Coh 𝕜 B s))
    (hF : FiniteDimensional 𝕜 (Coh 𝕜 (ssF_Fib p e₀) q)) :
    FiniteDimensional 𝕜 (S.E 2 ((s : ℤ), (q : ℤ))) := by
  obtain ⟨e2, _⟩ := hS
  haveI : FiniteDimensional 𝕜 (↥(Coh 𝕜 B s)) := hB
  haveI : FiniteDimensional 𝕜 (↥(Coh 𝕜 (ssF_Fib p e₀) q)) := hF
  exact LinearEquiv.finiteDimensional (e2 s q hs hq).toLinearEquiv.symm

/-! ## Propagation of finiteness and monotonicity of the dimensions along the pages -/

/-- Finiteness of the pages, inherited from page `2`, at a single bidegree. -/
theorem ssF_finiteDimensional_E_of (S : CohSS 𝕜) (a : ℤ × ℤ)
    (h : FiniteDimensional 𝕜 (S.E 2 a)) : ∀ k : ℕ, FiniteDimensional 𝕜 (S.E (k + 2) a) := by
  intro k
  induction k with
  | zero => simpa using h
  | succ k ih =>
      haveI := ih
      exact FiniteDimensional.of_surjective (S.proj (k + 2) a) (S.proj_surj (k + 2) a (by omega))

/-- The dimension does not increase along the pages, at a single bidegree. -/
theorem ssF_finrank_E_le_two (S : CohSS 𝕜) (a : ℤ × ℤ)
    (h : FiniteDimensional 𝕜 (S.E 2 a)) :
    ∀ k : ℕ, Module.finrank 𝕜 (S.E (k + 2) a) ≤ Module.finrank 𝕜 (S.E 2 a) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hk : FiniteDimensional 𝕜 (S.E (k + 2) a) := ssF_finiteDimensional_E_of S a h k
      exact (S.finrank_succ_le (r := k + 2) (by omega) a hk).trans ih

/-- Finiteness of `E_k^a` for `k ≥ 2`, from finiteness of `E_2^a`. -/
theorem ssF_finiteDimensional_E_of_le (S : CohSS 𝕜) (a : ℤ × ℤ) {k : ℕ} (hk : 2 ≤ k)
    (h : FiniteDimensional 𝕜 (S.E 2 a)) : FiniteDimensional 𝕜 (S.E k a) := by
  have hk' : k = k - 2 + 2 := (Nat.sub_add_cancel hk).symm
  rw [hk']
  exact ssF_finiteDimensional_E_of S a h (k - 2)

/-- The dimension bound `dim E_k^a ≤ dim E_2^a` for `k ≥ 2`. -/
theorem ssF_finrank_E_le_two' (S : CohSS 𝕜) (a : ℤ × ℤ) {k : ℕ} (hk : 2 ≤ k)
    (h : FiniteDimensional 𝕜 (S.E 2 a)) :
    Module.finrank 𝕜 (S.E k a) ≤ Module.finrank 𝕜 (S.E 2 a) := by
  have hk' : k = k - 2 + 2 := (Nat.sub_add_cancel hk).symm
  rw [hk']
  exact ssF_finrank_E_le_two S a h (k - 2)

/-! ## Coordinate bookkeeping for the row `q = 0` and the column `s = 0` -/

/-- The source bidegree of the differential hitting the row `q = 0` in degree `s`, in natural
coordinates. -/
theorem ssF_row0_sub_vr (s k : ℕ) (h1 : 1 ≤ k) (hk : k ≤ s) :
    (((s : ℤ), (0 : ℤ)) - vr k) = (((s - k : ℕ) : ℤ), (((k - 1 : ℕ)) : ℤ)) := by
  ext
  · simp only [vr, Prod.fst_sub]
    rw [Nat.cast_sub hk]
  · simp only [vr, Prod.snd_sub]
    rw [Nat.cast_sub h1]
    ring

/-- For `k > s` the source column of a differential hitting `(s,0)` is negative. -/
theorem ssF_row0_sub_vr_fst_neg (s k : ℕ) (hk : s < k) :
    ((((s : ℤ), (0 : ℤ)) - vr k).1) < 0 := by
  have h : (s : ℤ) < (k : ℤ) := by exact_mod_cast hk
  simp only [vr, Prod.fst_sub]
  omega

/-- No differential leaves the row `q = 0` in degree `s` at a page `k ≥ 2`. -/
theorem ssF_row0_add_vr_snd_neg (s k : ℕ) (hk : 2 ≤ k) :
    ((((s : ℤ), (0 : ℤ)) + vr k).2) < 0 := by
  have h : (2 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  simp only [vr, Prod.snd_add]
  omega

/-- The source of the page-`s` differential hitting `(s,0)` from the column `0`. -/
theorem ssF_row0_sub_vr_self (s : ℕ) (hs : 1 ≤ s) :
    (((s : ℤ), (0 : ℤ)) - vr s) = ((0 : ℤ), ((s - 1 : ℕ) : ℤ)) := by
  ext
  · simp only [vr, Prod.fst_sub]
    ring
  · simp only [vr, Prod.snd_sub]
    rw [Nat.cast_sub hs]
    ring

/-- The target of the page-`s` differential out of `(0,s-1)`. -/
theorem ssF_col_add_vr (s : ℕ) (hs : 1 ≤ s) :
    (((0 : ℤ), ((s - 1 : ℕ) : ℤ)) + vr s) = ((s : ℤ), (0 : ℤ)) := by
  ext
  · simp only [vr, Prod.fst_add]
    ring
  · simp only [vr, Prod.snd_add]
    rw [Nat.cast_sub hs]
    ring

/-! ## Parity helpers -/

/-- `Odd` is the negation of `Even` for natural numbers. -/
theorem ssF_odd_iff_not_even (k : ℕ) : Odd k ↔ ¬ Even k := by
  rw [Nat.odd_iff, Nat.not_even_iff]

/-- `Even 0`. -/
theorem ssF_even_zero : Even (0 : ℕ) := ⟨0, by norm_num⟩

/-! ## Survival of a class through several pages -/

/-- **Survival of a nonzero class through `t` pages.**  If `x ∈ E_r^a` is nonzero, nothing hits `a`
on the pages `r ≤ k < r + t` (the incoming differential is zero), and nothing leaves `a` on any page
`k ≥ r`, then `E_{r+t}^a ≠ 0`. -/
theorem ssF_exists_ne_zero_iterate_of_dzero (S : CohSS 𝕜) {r : ℕ} (hr : 2 ≤ r) (a : ℤ × ℤ)
    {t : ℕ} (x : S.E r a) (hx0 : x ≠ 0)
    (hsrc : ∀ k : ℕ, r ≤ k → k < r + t → S.d k (a - vr k) a = 0)
    (htgt : ∀ k : ℕ, r ≤ k → IsZero (S.E k (a + vr k))) :
    ∃ y : S.E (r + t) a, y ≠ 0 := by
  have aux : ∀ i : ℕ, i ≤ t → ∃ y : S.E (r + i) a, y ≠ 0 := by
    intro i
    induction i with
    | zero => intro _; exact ⟨x, hx0⟩
    | succ i ih =>
        intro hi
        obtain ⟨y, hy0⟩ := ih (by omega)
        have hri : 2 ≤ r + i := by omega
        have hd : S.d (r + i) a (a + vr (r + i)) = 0 :=
          S.d_eq_zero_of_isZero (htgt (r + i) (by omega))
        have hyc : (S.d (r + i) a (a + vr (r + i))).hom y = 0 := by rw [hd]; rfl
        refine ⟨S.proj (r + i) a ⟨y, hyc⟩, ?_⟩
        intro h0
        have hmem : y ∈ LinearMap.range (S.d (r + i) (a - vr (r + i)) a).hom :=
          (S.proj_ker (r + i) a hri ⟨y, hyc⟩).mp h0
        rw [hsrc (r + i) (by omega) (by omega)] at hmem
        exact hy0 (by simpa [LinearMap.range_zero] using hmem)
  obtain ⟨y, hy0⟩ := aux t le_rfl
  exact ⟨y, hy0⟩

/-! ## The differential out of column `0` -/

/-- **A surviving class of the column `0` forces `d_s^{0,q} = 0`.** -/
theorem ssF_d_col_eq_zero_of_survives (S : CohSS 𝕜) {s q : ℕ} (hs : 2 ≤ s)
    (hfin2 : FiniteDimensional 𝕜 (S.E 2 ((0 : ℤ), (q : ℤ))))
    (hle1 : Module.finrank 𝕜 (S.E 2 ((0 : ℤ), (q : ℤ))) ≤ 1)
    (hz : ∃ z : S.E (s + 1) ((0 : ℤ), (q : ℤ)), z ≠ 0) :
    S.d s ((0 : ℤ), (q : ℤ)) (((0 : ℤ), (q : ℤ)) + vr s) = 0 := by
  set a : ℤ × ℤ := ((0 : ℤ), (q : ℤ)) with ha
  have hfin_s : FiniteDimensional 𝕜 (S.E s a) := ssF_finiteDimensional_E_of_le S a hs hfin2
  have hle : Module.finrank 𝕜 (S.E s a) ≤ 1 :=
    (ssF_finrank_E_le_two' S a hs hfin2).trans hle1
  obtain ⟨z, hz0⟩ := hz
  obtain ⟨w, hw⟩ := S.proj_surj s a hs z
  have hwne : w ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hw
    exact hz0 hw.symm
  have hw0 : (w : S.E s a) ≠ 0 := fun h => hwne (Subtype.ext h)
  have hne : ¬ IsZero (S.E s a) :=
    ssF_not_isZero_of_exists_ne_zero ⟨(w : S.E s a), hw0⟩
  haveI : Nontrivial (S.E s a) := (ssF_not_isZero_iff_nontrivial _).mp hne
  have hpos : 0 < Module.finrank 𝕜 (S.E s a) := ssF_finrank_pos hfin_s hne
  have hdim1 : Module.finrank 𝕜 (S.E s a) = 1 := le_antisymm hle hpos
  have hdz : ∀ y : S.E s a, (S.d s a (a + vr s)).hom y = 0 := by
    intro y
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hdim1 hw0 y
    rw [← hc, map_smul, w.2, smul_zero]
  have hdz' : (S.d s a (a + vr s)).hom = 0 := LinearMap.ext hdz
  exact ModuleCat.hom_ext (by rw [hdz', ModuleCat.hom_zero])

/-! ## `H^0` of the base -/

/-- **`H^0(B)` is one-dimensional.** -/
theorem ssF_finrank_Coh_zero {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (S : CohSS 𝕜) (p : C(E, B)) (e₀ : E) (N : ℕ) (hS : IsSerreMSS S p e₀ N)
    (hF1 : Module.finrank 𝕜 (Coh 𝕜 (ssF_Fib p e₀) 0) = 1)
    (hE1 : Module.finrank 𝕜 (Coh 𝕜 E 0) = 1) :
    Module.finrank 𝕜 (Coh 𝕜 B 0) = 1 := by
  obtain ⟨e2, _, _, hconv, _, _⟩ := hS
  have h0 : Module.finrank 𝕜 (S.E 2 (((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ))) = 1 := by
    have h := (hconv 0 (Nat.zero_le N)).trans hE1
    simpa using h
  have h1 : Module.finrank 𝕜 (S.E 2 (((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ))) =
      Module.finrank 𝕜 (Coh 𝕜 B 0) * Module.finrank 𝕜 (Coh 𝕜 (ssF_Fib p e₀) 0) := by
    rw [LinearEquiv.finrank_eq (e2 0 0 (by omega) (by omega)).toLinearEquiv]
    rw [Module.finrank_tensorProduct]
  rw [h1, hF1, mul_one] at h0
  exact h0

/-! ## Part (A) -/

theorem ssF_partA {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e₀ : E)
    (N : ℕ) (S : CohSS 𝕜) (hS : IsSerreMSS S p e₀ N)
    (hFib : ∀ q : ℕ, 0 < q → q ≤ N → IsZero (Coh 𝕜 (ssF_Fib p e₀) q))
    (hF0 : Nontrivial (Coh 𝕜 (ssF_Fib p e₀) 0))
    (hE : ∀ n : ℕ, 0 < n → n ≤ N → Subsingleton (Coh 𝕜 E n)) :
    ∀ s : ℕ, 0 < s → s ≤ N → IsZero (Coh 𝕜 B s) := by
  have hS' : IsSerreMSS S p e₀ N := hS
  obtain ⟨_, _, hconv, _, _, _⟩ := hS'
  have hF0ne : ¬ IsZero (Coh 𝕜 (ssF_Fib p e₀) 0) :=
    (ssF_not_isZero_iff_nontrivial _).mpr hF0
  intro s
  refine Nat.strongRecOn (motive := fun n : ℕ => 0 < n → n ≤ N → IsZero (Coh 𝕜 B n)) s ?_
  intro s ih hs0 hsN
  by_contra hne
  have hE2ne : ¬ IsZero (S.E 2 ((s : ℤ), (0 : ℤ))) :=
    ssF_e2_not_isZero S p e₀ N hS (s := s) (q := 0) (by omega) (by omega) hne hF0ne
  obtain ⟨x, hx0⟩ := ssF_exists_ne_zero_of_not_isZero hE2ne
  have htgt : ∀ k : ℕ, 2 ≤ k → IsZero (S.E k (((s : ℤ), (0 : ℤ)) + vr k)) :=
    fun k hk => S.isZero_quad k _ (Or.inr (ssF_row0_add_vr_snd_neg s k hk))
  have hsrc : ∀ k : ℕ, 2 ≤ k → k < 2 + s →
      S.d k (((s : ℤ), (0 : ℤ)) - vr k) ((s : ℤ), (0 : ℤ)) = 0 := by
    intro k hk2 hklt
    by_cases hks : k ≤ s
    · have hz : IsZero (S.E k (((s : ℤ), (0 : ℤ)) - vr k)) := by
        rw [ssF_row0_sub_vr s k (by omega) hks]
        have hzF : IsZero (Coh 𝕜 (ssF_Fib p e₀) (k - 1)) :=
          hFib (k - 1) (by omega) (by omega)
        have h2 : IsZero (S.E 2 (((s - k : ℕ) : ℤ), ((k - 1 : ℕ) : ℤ))) :=
          ssF_e2_isZero_of_right S p e₀ N hS (s := s - k) (q := k - 1) (by omega) (by omega) hzF
        have h3 := S.isZero_two_of _ h2 (k - 2)
        rwa [Nat.sub_add_cancel hk2] at h3
      exact hz.eq_of_src _ _
    · have hz : IsZero (S.E k (((s : ℤ), (0 : ℤ)) - vr k)) :=
        S.isZero_quad k _ (Or.inl (ssF_row0_sub_vr_fst_neg s k (by omega)))
      exact hz.eq_of_src _ _
  obtain ⟨y, hy0⟩ := ssF_exists_ne_zero_iterate_of_dzero S (r := 2) (a := ((s : ℤ), (0 : ℤ)))
    (t := s) (by omega) x hx0 hsrc htgt
  have hzero : IsZero (S.E (2 + s) ((s : ℤ), ((0 : ℕ) : ℤ))) := by
    have h := hconv s (by omega) hsN (hE s hs0 hsN) s 0 (by omega)
    rw [show s + 2 = 2 + s from by omega] at h
    exact h
  haveI : Subsingleton (↥(S.E (2 + s) ((s : ℤ), ((0 : ℕ) : ℤ)))) :=
    ModuleCat.subsingleton_of_isZero hzero
  exact hy0 (Subsingleton.elim y 0)

/-! ## Part (B) -/

theorem ssF_partB {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e₀ : E)
    (N : ℕ) (S : CohSS 𝕜) (hS : IsSerreMSS S p e₀ N)
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜 (Coh 𝕜 (ssF_Fib p e₀) q) ∧
      FiniteDimensional 𝕜 (Coh 𝕜 E q))
    (hfinB : ∀ s : ℕ, s ≤ N → FiniteDimensional 𝕜 (Coh 𝕜 B s))
    (hEO : ∀ q : ℕ, q ≤ N →
      ((Even q → Nonempty (Coh 𝕜 (ssF_Fib p e₀) q ≅ ModuleCat.of 𝕜 𝕜) ∧
        Nonempty (Coh 𝕜 E q ≅ ModuleCat.of 𝕜 𝕜)) ∧
       (Odd q → IsZero (Coh 𝕜 (ssF_Fib p e₀) q) ∧ IsZero (Coh 𝕜 E q))))
    (hsurv : ∀ q : ℕ, 2 ≤ q → q ≤ N → Even q → ∃ z : S.E (q + 2) (0, (q : ℤ)), z ≠ 0) :
    ∀ s : ℕ, 0 < s → s ≤ N → IsZero (Coh 𝕜 B s) := by
  have hS' : IsSerreMSS S p e₀ N := hS
  obtain ⟨_, _, hconv0, hconv, _, _⟩ := hS'
  have hFev : ∀ q : ℕ, q ≤ N → Even q → ¬ IsZero (Coh 𝕜 (ssF_Fib p e₀) q) :=
    fun q hq hqE => ssF_not_isZero_of_iso_k ((hEO q hq).1 hqE).1
  have hFev1 : ∀ q : ℕ, q ≤ N → Even q → Module.finrank 𝕜 (Coh 𝕜 (ssF_Fib p e₀) q) = 1 :=
    fun q hq hqE => ssF_finrank_eq_one_of_iso_k ((hEO q hq).1 hqE).1
  have hEev1 : ∀ q : ℕ, q ≤ N → Even q → Module.finrank 𝕜 (Coh 𝕜 E q) = 1 :=
    fun q hq hqE => ssF_finrank_eq_one_of_iso_k ((hEO q hq).1 hqE).2
  intro s
  refine Nat.strongRecOn (motive := fun n : ℕ => 0 < n → n ≤ N → IsZero (Coh 𝕜 B n)) s ?_
  intro s ih hs0 hsN
  by_contra hne
  have hF0ne : ¬ IsZero (Coh 𝕜 (ssF_Fib p e₀) 0) := hFev 0 (by omega) ssF_even_zero
  have hE2ne : ¬ IsZero (S.E 2 ((s : ℤ), (0 : ℤ))) :=
    ssF_e2_not_isZero S p e₀ N hS (s := s) (q := 0) (by omega) (by omega) hne hF0ne
  obtain ⟨x, hx0⟩ := ssF_exists_ne_zero_of_not_isZero hE2ne
  have htgt : ∀ k : ℕ, 2 ≤ k → IsZero (S.E k (((s : ℤ), (0 : ℤ)) + vr k)) :=
    fun k hk => S.isZero_quad k _ (Or.inr (ssF_row0_add_vr_snd_neg s k hk))
  by_cases hse : Even s
  · -- even total degree
    have hsrc : ∀ k : ℕ, 2 ≤ k → k < 2 + s →
        S.d k (((s : ℤ), (0 : ℤ)) - vr k) ((s : ℤ), (0 : ℤ)) = 0 := by
      intro k hk2 hklt
      by_cases hks : k ≤ s
      · have hz : IsZero (S.E k (((s : ℤ), (0 : ℤ)) - vr k)) := by
          rw [ssF_row0_sub_vr s k (by omega) hks]
          by_cases hke : Even k
          · have hod : Odd (k - 1) := by
              obtain ⟨m, hm⟩ := hke
              exact ⟨m - 1, by omega⟩
            have hzF : IsZero (Coh 𝕜 (ssF_Fib p e₀) (k - 1)) :=
              ((hEO (k - 1) (by omega)).2 hod).1
            have h2 : IsZero (S.E 2 (((s - k : ℕ) : ℤ), ((k - 1 : ℕ) : ℤ))) :=
              ssF_e2_isZero_of_right S p e₀ N hS (s := s - k) (q := k - 1) (by omega) (by omega) hzF
            have h3 := S.isZero_two_of _ h2 (k - 2)
            rwa [Nat.sub_add_cancel hk2] at h3
          · have hod : Odd k := (ssF_odd_iff_not_even k).mpr hke
            have hklts : k < s := by
              rcases lt_or_eq_of_le hks with h | h
              · exact h
              · exfalso
                rw [← h] at hse
                exact (ssF_odd_iff_not_even k).mp hod hse
            have hzB : IsZero (Coh 𝕜 B (s - k)) := ih (s - k) (by omega) (by omega) (by omega)
            have h2 : IsZero (S.E 2 (((s - k : ℕ) : ℤ), ((k - 1 : ℕ) : ℤ))) :=
              ssF_e2_isZero_of_left S p e₀ N hS (s := s - k) (q := k - 1) (by omega) (by omega) hzB
            have h3 := S.isZero_two_of _ h2 (k - 2)
            rwa [Nat.sub_add_cancel hk2] at h3
        exact hz.eq_of_src _ _
      · have hz : IsZero (S.E k (((s : ℤ), (0 : ℤ)) - vr k)) :=
          S.isZero_quad k _ (Or.inl (ssF_row0_sub_vr_fst_neg s k (by omega)))
        exact hz.eq_of_src _ _
    obtain ⟨y, hy0⟩ := ssF_exists_ne_zero_iterate_of_dzero S (r := 2)
      (a := ((s : ℤ), (0 : ℤ))) (t := s) (by omega) x hx0 hsrc htgt
    have hs2 : 2 ≤ s := by
      obtain ⟨m, hm⟩ := hse
      omega
    have hzs : ∃ z : S.E (s + 2) (0, (s : ℤ)), z ≠ 0 := hsurv s hs2 hsN hse
    -- the summands `s' = 0` and `s' = s` of the diagonal in total degree `s`
    have hb0 : (((0 : ℕ) : ℤ), ((s - 0 : ℕ) : ℤ)) = (((0 : ℕ) : ℤ), ((s : ℕ) : ℤ)) := by
      simp only [Nat.sub_zero]
    have hbs : (((s : ℕ) : ℤ), ((s - s : ℕ) : ℤ)) = (((s : ℕ) : ℤ), ((0 : ℕ) : ℤ)) := by
      simp only [Nat.sub_self]
    have hfd0 : FiniteDimensional 𝕜 (S.E (s + 2) (((0 : ℕ) : ℤ), ((s - 0 : ℕ) : ℤ))) := by
      rw [hb0]
      exact ssF_finiteDimensional_E_of_le S (((0 : ℕ) : ℤ), ((s : ℕ) : ℤ)) (k := s + 2) (by omega)
        (ssF_finiteDimensional_E2 S p e₀ N hS (s := 0) (q := s) (by omega) hsN
          (hfinB 0 (by omega)) (hfin s hsN).1)
    have hne0 : ¬ IsZero (S.E (s + 2) (((0 : ℕ) : ℤ), ((s - 0 : ℕ) : ℤ))) := by
      intro hz
      rw [hb0] at hz
      obtain ⟨z, hz0⟩ := hzs
      exact hz0 ((ModuleCat.subsingleton_of_isZero hz).elim z 0)
    have hf0 : 0 < Module.finrank 𝕜 (S.E (s + 2) (((0 : ℕ) : ℤ), ((s - 0 : ℕ) : ℤ))) :=
      ssF_finrank_pos hfd0 hne0
    have hfds : FiniteDimensional 𝕜 (S.E (s + 2) (((s : ℕ) : ℤ), ((s - s : ℕ) : ℤ))) := by
      rw [hbs]
      exact ssF_finiteDimensional_E_of_le S (((s : ℕ) : ℤ), ((0 : ℕ) : ℤ)) (k := s + 2) (by omega)
        (ssF_finiteDimensional_E2 S p e₀ N hS (s := s) (q := 0) (by omega) (by omega)
          (hfinB s hsN) (hfin 0 (by omega)).1)
    have hnes : ¬ IsZero (S.E (s + 2) (((s : ℕ) : ℤ), ((s - s : ℕ) : ℤ))) := by
      intro hz
      rw [hbs] at hz
      have hz' : IsZero (S.E (2 + s) (((s : ℕ) : ℤ), ((0 : ℕ) : ℤ))) := by
        rw [show s + 2 = 2 + s from by omega] at hz
        exact hz
      exact hy0 ((ModuleCat.subsingleton_of_isZero hz').elim y 0)
    have hfs : 0 < Module.finrank 𝕜 (S.E (s + 2) (((s : ℕ) : ℤ), ((s - s : ℕ) : ℤ))) :=
      ssF_finrank_pos hfds hnes
    have hsum : (∑ i ∈ Finset.range (s + 1),
          Module.finrank 𝕜 (S.E (s + 2) ((i : ℤ), ((s - i : ℕ) : ℤ)))) = 1 := by
      rw [hconv s hsN, hEev1 s hsN hse]
    rw [Finset.sum_range_succ] at hsum
    have hle0 : Module.finrank 𝕜 (S.E (s + 2) (((0 : ℕ) : ℤ), ((s - 0 : ℕ) : ℤ))) ≤
        ∑ i ∈ Finset.range s,
          Module.finrank 𝕜 (S.E (s + 2) ((i : ℤ), ((s - i : ℕ) : ℤ))) :=
      Finset.single_le_sum (f := fun i : ℕ =>
          Module.finrank 𝕜 (S.E (s + 2) ((i : ℤ), ((s - i : ℕ) : ℤ))))
        (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr hs0)
    exfalso
    omega
  · -- odd total degree
    have hso : Odd s := (ssF_odd_iff_not_even s).mpr hse
    have hsrc : ∀ k : ℕ, 2 ≤ k → k < 2 + s →
        S.d k (((s : ℤ), (0 : ℤ)) - vr k) ((s : ℤ), (0 : ℤ)) = 0 := by
      intro k hk2 hklt
      by_cases hks : k ≤ s
      · by_cases hks' : k < s
        · have hz : IsZero (S.E k (((s : ℤ), (0 : ℤ)) - vr k)) := by
            rw [ssF_row0_sub_vr s k (by omega) hks]
            by_cases hke : Even k
            · have hod : Odd (k - 1) := by
                obtain ⟨m, hm⟩ := hke
                exact ⟨m - 1, by omega⟩
              have hzF : IsZero (Coh 𝕜 (ssF_Fib p e₀) (k - 1)) :=
                ((hEO (k - 1) (by omega)).2 hod).1
              have h2 : IsZero (S.E 2 (((s - k : ℕ) : ℤ), ((k - 1 : ℕ) : ℤ))) :=
                ssF_e2_isZero_of_right S p e₀ N hS (s := s - k) (q := k - 1) (by omega) (by omega) hzF
              have h3 := S.isZero_two_of _ h2 (k - 2)
              rwa [Nat.sub_add_cancel hk2] at h3
            · have hod : Odd k := (ssF_odd_iff_not_even k).mpr hke
              have hzB : IsZero (Coh 𝕜 B (s - k)) :=
                ih (s - k) (by omega) (by omega) (by omega)
              have h2 : IsZero (S.E 2 (((s - k : ℕ) : ℤ), ((k - 1 : ℕ) : ℤ))) :=
                ssF_e2_isZero_of_left S p e₀ N hS (s := s - k) (q := k - 1) (by omega) (by omega) hzB
              have h3 := S.isZero_two_of _ h2 (k - 2)
              rwa [Nat.sub_add_cancel hk2] at h3
          exact hz.eq_of_src _ _
        · -- here `k = s`: the page-`s` differential out of the column `0`
          have hks_eq : k = s := by omega
          have hs3 : 3 ≤ s := by
            obtain ⟨m, hm⟩ := hso
            omega
          have hEven_sm1 : Even (s - 1) := by
            obtain ⟨m, hm⟩ := hso
            exact ⟨m, by omega⟩
          have hzcol : ∃ z : S.E (s + 1) ((0 : ℤ), ((s - 1 : ℕ) : ℤ)), z ≠ 0 := by
            have h := hsurv (s - 1) (by omega) (by omega) hEven_sm1
            have hkey : (s - 1) + 2 = s + 1 := by omega
            rw [hkey] at h
            exact h
          have hCoh0 : Module.finrank 𝕜 (Coh 𝕜 B 0) = 1 :=
            ssF_finrank_Coh_zero S p e₀ N hS (hFev1 0 (by omega) ssF_even_zero)
              (hEev1 0 (by omega) ssF_even_zero)
          have hfin2col : FiniteDimensional 𝕜 (S.E 2 ((0 : ℤ), ((s - 1 : ℕ) : ℤ))) :=
            ssF_finiteDimensional_E2 S p e₀ N hS (s := 0) (q := s - 1) (by omega) (by omega)
              (hfinB 0 (by omega)) (hfin (s - 1) (by omega)).1
          have hdimcol : Module.finrank 𝕜 (S.E 2 (((0 : ℕ) : ℤ), ((s - 1 : ℕ) : ℤ))) = 1 := by
            rw [ssF_e2_finrank S p e₀ N hS (s := 0) (q := s - 1) (by omega) (by omega), hCoh0,
              hFev1 (s - 1) (by omega) hEven_sm1]
          have hd := ssF_d_col_eq_zero_of_survives S (s := s) (q := s - 1) (by omega) hfin2col
            (le_of_eq hdimcol) hzcol
          rw [ssF_col_add_vr s (by omega)] at hd
          rw [hks_eq, ssF_row0_sub_vr_self s (by omega)]
          exact hd
      · have hz : IsZero (S.E k (((s : ℤ), (0 : ℤ)) - vr k)) :=
          S.isZero_quad k _ (Or.inl (ssF_row0_sub_vr_fst_neg s k (by omega)))
        exact hz.eq_of_src _ _
    obtain ⟨y, hy0⟩ := ssF_exists_ne_zero_iterate_of_dzero S (r := 2)
      (a := ((s : ℤ), (0 : ℤ))) (t := s) (by omega) x hx0 hsrc htgt
    have hsub : Subsingleton (↥(Coh 𝕜 E s)) :=
      ModuleCat.subsingleton_of_isZero ((hEO s hsN).2 hso).2
    have hzero : IsZero (S.E (2 + s) ((s : ℤ), ((0 : ℕ) : ℤ))) := by
      have h := hconv0 s (by omega) hsN hsub s 0 (by omega)
      rw [show s + 2 = 2 + s from by omega] at h
      exact h
    haveI : Subsingleton (↥(S.E (2 + s) ((s : ℤ), ((0 : ℕ) : ℤ)))) :=
      ModuleCat.subsingleton_of_isZero hzero
    exact hy0 (Subsingleton.elim y 0)

/-! ## The forcing lemma -/

/-- **Forcing lemmas for the multiplicative Serre spectral sequence over a field** (the toolkit `Work.Pi6.CohSS.isZero_two_of`, `Work.Pi6.CohSS.finrank_le_next`, `Work.Pi6.CohSS.not_isZero_of_survives`, `Work.Pi6.CohSS.tmul_ne_zero_of_ne_zero` of `Submission/Work/Pi6/EMM2/SSKit.lean` is available).

(A) If the fibre has trivial cohomology in positive degrees `≤ N` and the total space has trivial cohomology in degrees `1 … N`, then the base has trivial cohomology in degrees `1 … N`: for `s` minimal with `H^s(B) ≠ 0` the term `E_2^{s,0} ≅ H^s(B) ⊗ H^0(F)` is non-zero and has no incoming differential (every source `(s-r, r-1)`, `r ≥ 2`, has `0 < r-1 ≤ N`, hence vanishes), so it survives to `E_{s+2}^{s,0}`, contradicting `conv_zero`.

(B) If fibre and total both have one-dimensional cohomology in every even degree `≤ N`, vanish in odd degrees, all are finite dimensional (the *base* as well — this finiteness is needed for the dimension count), and the fibre classes survive in even degrees (`∃ z ≠ 0` in `E_{q+2}^{0,q}` — what `IsSerreMSS`'s fibre edge gives when the fibre restriction is onto), then the base has trivial cohomology in degrees `1 … N`: for `s` minimal with `H^s(B) ≠ 0`, in the even case both `E_{s+2}^{0,s}` and `E_{s+2}^{s,0}` are non-zero, contradicting `conv_dim` `∑_{s'} dim E_{s+2}^{s',s-s'} = dim H^s(E) = 1`; in the odd case the incoming differential into `(s,0)` from column `0` is zero by the survival hypothesis, so `E_{s+2}^{s,0} ≠ 0` while `dim H^s(E) = 0`. (`H^0(B) ≅ 𝕜` follows from `conv_dim` at `n = 0` together with `E_2^{0,0} ≅ H^0(B) ⊗ H^0(F)`.) -/
theorem ssForcing {𝕜 : Type} [Field 𝕜] :
    (∀ {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (N : ℕ)
        (S : Work.Pi6.CohSS 𝕜), Work.Pi6.IsSerreMSS S p e₀ N →
        (∀ q : ℕ, 0 < q → q ≤ N →
          CategoryTheory.Limits.IsZero (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) →
        Nontrivial (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) 0) →
        (∀ n : ℕ, 0 < n → n ≤ N → Subsingleton (Work.Pi6.Coh 𝕜 E n)) →
        (∀ s : ℕ, 0 < s → s ≤ N →
          CategoryTheory.Limits.IsZero (Work.Pi6.Coh 𝕜 B s))) ∧
      (∀ {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (N : ℕ)
        (S : Work.Pi6.CohSS 𝕜), Work.Pi6.IsSerreMSS S p e₀ N →
        (∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜 (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) ∧
          FiniteDimensional 𝕜 (Work.Pi6.Coh 𝕜 E q)) →
        (∀ s : ℕ, s ≤ N → FiniteDimensional 𝕜 (Work.Pi6.Coh 𝕜 B s)) →
        (∀ q : ℕ, q ≤ N →
          ((Even q → Nonempty (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q ≅ ModuleCat.of 𝕜 𝕜) ∧
            Nonempty (Work.Pi6.Coh 𝕜 E q ≅ ModuleCat.of 𝕜 𝕜)) ∧
          (Odd q → CategoryTheory.Limits.IsZero (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) ∧
            CategoryTheory.Limits.IsZero (Work.Pi6.Coh 𝕜 E q)))) →
        (∀ q : ℕ, 2 ≤ q → q ≤ N → Even q → ∃ z : S.E (q + 2) (0, (q : ℤ)), z ≠ 0) →
        (∀ s : ℕ, 0 < s → s ≤ N →
          CategoryTheory.Limits.IsZero (Work.Pi6.Coh 𝕜 B s))) := by
  exact ⟨ssF_partA, ssF_partB⟩

end

end Work.Pi6.EMODD
