import Mathlib
import Submission.Work.Higman.Q3.Defs
import Submission.Work.Higman.cocycle_setup
import Submission.Work.Higman.Q3.card_irreducible
import Submission.Work.Higman.twoStep_q2_normal_form
import Submission.Work.Higman.Q3.L12.q2xi_basic
import Submission.Work.Higman.Q3.orderOf_dvd_ncard_of_semiregular
import Submission.Work.Higman.Q3.pow_sub_one_dvd_pow_sub_one_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.Higman.Q3.L12

open Work.Higman

/-! ## The irreducible case is impossible

A self-contained copy of the linear-algebra crux: a finite `𝔽₂`-space of cardinality `2 ^ (2n)`
with an endomorphism `T` satisfying `T ^ (2 ^ n) = T` and no proper non-zero invariant subspace
cannot exist.  -/

section Crux

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- In an exponent-two group, `a + a = 0`. -/
theorem two_add_self (a : V) : a + a = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [← two_smul (ZMod 2) a, h2, zero_smul]

/-- **The minimal polynomial is irreducible** when the only invariant subspaces are `⊥` and
`⊤`: a non-trivial factorisation `m = f * g` gives the non-zero proper invariant subspace
`ker (f (T))`. -/
theorem irreducible_minpoly_of_irreducible [Nontrivial V] (T : V →ₗ[ZMod 2] V)
    (hirr : ∀ U : Submodule (ZMod 2) V, (∀ u ∈ U, T u ∈ U) → U = ⊥ ∨ U = ⊤) :
    Irreducible (minpoly (ZMod 2) T) := by
  classical
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  set m : Polynomial (ZMod 2) := minpoly (ZMod 2) T with hm
  have hm_ne : m ≠ 0 := by rw [hm]; exact minpoly.ne_zero (LinearMap.isIntegral T)
  have hmnat : 0 < m.natDegree := by
    rw [hm]; exact minpoly.natDegree_pos (LinearMap.isIntegral T)
  have hunit : ∀ p : Polynomial (ZMod 2), p ≠ 0 → p.natDegree = 0 → IsUnit p := by
    intro p hp0 hp
    refine Polynomial.isUnit_iff_degree_eq_zero.mpr ?_
    rw [Polynomial.degree_eq_natDegree hp0, hp]
    rfl
  refine ⟨?_, ?_⟩
  · intro hunitm
    have hdeg : m.degree = 0 := Polynomial.isUnit_iff_degree_eq_zero.mp hunitm
    have h0 : m.natDegree = 0 := Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr (by rw [hdeg])
    omega
  · rintro f g hfg
    by_contra hcon
    push_neg at hcon
    obtain ⟨hfnu, hgnu⟩ := hcon
    have hf0 : f ≠ 0 := by rintro rfl; rw [zero_mul] at hfg; exact hm_ne hfg
    have hg0 : g ≠ 0 := by rintro rfl; rw [mul_zero] at hfg; exact hm_ne hfg
    have hfpos : 0 < f.natDegree := by
      rcases Nat.eq_zero_or_pos f.natDegree with h | h
      · exact absurd (hunit f hf0 h) hfnu
      · exact h
    have hgpos : 0 < g.natDegree := by
      rcases Nat.eq_zero_or_pos g.natDegree with h | h
      · exact absurd (hunit g hg0 h) hgnu
      · exact h
    have hmdeg : m.natDegree = f.natDegree + g.natDegree := by
      rw [hfg, Polynomial.natDegree_mul hf0 hg0]
    have hfd : f.natDegree < m.natDegree := by omega
    have hgd : g.natDegree < m.natDegree := by omega
    have hfT : Polynomial.aeval T f ≠ 0 := by
      intro h0
      have hdiv : minpoly (ZMod 2) T ∣ f := minpoly.dvd (ZMod 2) T h0
      rw [← hm] at hdiv
      have hle := Polynomial.natDegree_le_of_dvd hdiv hf0
      omega
    have hgT : Polynomial.aeval T g ≠ 0 := by
      intro h0
      have hdiv : minpoly (ZMod 2) T ∣ g := minpoly.dvd (ZMod 2) T h0
      rw [← hm] at hdiv
      have hle := Polynomial.natDegree_le_of_dvd hdiv hg0
      omega
    set φ : V →ₗ[ZMod 2] V := Polynomial.aeval T f with hφ
    have hcomp : φ * Polynomial.aeval T g = Polynomial.aeval T m := by
      rw [hφ, ← map_mul, hfg]
    have hker0 : LinearMap.ker φ ≠ ⊥ := by
      obtain ⟨v, hv⟩ : ∃ v : V, (Polynomial.aeval T g) v ≠ 0 := by
        by_contra h
        push_neg at h
        exact hgT (LinearMap.ext h)
      intro hbot
      refine hv ?_
      have hmem : (Polynomial.aeval T g) v ∈ LinearMap.ker φ := by
        rw [LinearMap.mem_ker]
        have h2 := congrArg (fun (ψ : Module.End (ZMod 2) V) => ψ v) hcomp
        rw [Module.End.mul_apply] at h2
        rw [h2, show (Polynomial.aeval T m) v = 0 from by rw [minpoly.aeval]; rfl]
      rw [hbot] at hmem
      simpa using hmem
    have hker1 : LinearMap.ker φ ≠ ⊤ := by
      intro htop
      refine hfT (LinearMap.ext fun v => ?_)
      have hv : v ∈ LinearMap.ker φ := by rw [htop]; trivial
      rw [LinearMap.mem_ker] at hv
      simpa using hv
    have hkerinv : ∀ u ∈ LinearMap.ker φ, T u ∈ LinearMap.ker φ := by
      intro u hu
      rw [LinearMap.mem_ker] at hu ⊢
      have hcomm : φ * T = T * φ := by
        have h1 : φ * T = Polynomial.aeval T (f * Polynomial.X) := by
          rw [hφ, map_mul, Polynomial.aeval_X]
        have h2 : T * φ = Polynomial.aeval T (Polynomial.X * f) := by
          rw [hφ, map_mul, Polynomial.aeval_X]
        rw [h1, h2, mul_comm]
      have h3 := congrArg (fun (ψ : Module.End (ZMod 2) V) => ψ u) hcomm
      rw [Module.End.mul_apply, Module.End.mul_apply, hu] at h3
      rw [h3, map_zero T]
    rcases hirr (LinearMap.ker φ) hkerinv with h | h
    · exact hker0 h
    · exact hker1 h

/-- **The spanning bound.**  In the irreducible case, `finrank V ≤ natDegree (minpoly T)`: for
`x ≠ 0` the iterates `x, T x, …, T ^ (natDegree m - 1) x` span an invariant subspace. -/
theorem finrank_le_natDegree_minpoly [Nontrivial V] (T : V →ₗ[ZMod 2] V)
    (hirr : ∀ U : Submodule (ZMod 2) V, (∀ u ∈ U, T u ∈ U) → U = ⊥ ∨ U = ⊤) :
    Module.finrank (ZMod 2) V ≤ (minpoly (ZMod 2) T).natDegree := by
  classical
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨x, hx⟩ : ∃ x : V, x ≠ 0 := exists_ne 0
  set m : Polynomial (ZMod 2) := minpoly (ZMod 2) T with hm
  set d : ℕ := m.natDegree with hd
  have hm_monic : m.Monic := by rw [hm]; exact minpoly.monic (LinearMap.isIntegral T)
  have hdpos : 0 < d := by
    rw [hd, hm]; exact minpoly.natDegree_pos (LinearMap.isIntegral T)
  set S : Set V := Set.range (fun j : Fin d => (T ^ (j : ℕ)) x) with hS
  -- the coefficient expansion of `m (T) x`
  have hcoeff : (Polynomial.aeval T m) x
      = ∑ i ∈ Finset.range (d + 1), m.coeff i • ((T ^ i) x) := by
    have h := Polynomial.aeval_eq_sum_range (p := m) T
    have h2 := congrArg (fun (ψ : Module.End (ZMod 2) V) => ψ x) h
    rw [LinearMap.sum_apply] at h2
    simp only [LinearMap.smul_apply] at h2
    simpa only [hd] using h2
  have hcd : m.coeff d = 1 := by
    simpa only [hd] using hm_monic.coeff_natDegree
  have hzero : (0 : V) = (∑ i ∈ Finset.range d, m.coeff i • ((T ^ i) x)) +
      m.coeff d • ((T ^ d) x) := by
    rw [← Finset.sum_range_succ, ← hcoeff]
    show (0 : V) = (Polynomial.aeval T m) x
    rw [minpoly.aeval]
    rfl
  have hTd_eq : (T ^ d) x = ∑ i ∈ Finset.range d, m.coeff i • ((T ^ i) x) := by
    rw [hcd, one_smul] at hzero
    have hAB : (T ^ d) x + (∑ i ∈ Finset.range d, m.coeff i • ((T ^ i) x)) = 0 := by
      rw [add_comm]; exact hzero.symm
    have hneg : -((T ^ d) x) = ∑ i ∈ Finset.range d, m.coeff i • ((T ^ i) x) :=
      neg_eq_iff_add_eq_zero.mpr hAB
    rw [← neg_eq_iff_add_eq_zero.mpr (two_add_self ((T ^ d) x)), hneg]
  have hTd : (T ^ d) x ∈ Submodule.span (ZMod 2) S := by
    rw [hTd_eq]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩
  -- the span of `S` is invariant
  have hgen : ∀ u ∈ S, T u ∈ Submodule.span (ZMod 2) S := by
    rintro u ⟨j, rfl⟩
    have hj := j.isLt
    by_cases hjc : (j : ℕ) + 1 < d
    · refine Submodule.subset_span ⟨⟨(j : ℕ) + 1, hjc⟩, ?_⟩
      show (T ^ ((j : ℕ) + 1)) x = T ((T ^ (j : ℕ)) x)
      rw [pow_succ', Module.End.mul_apply]
    · have hj' : (j : ℕ) + 1 = d := by omega
      have : T ((fun j : Fin d => (T ^ (j : ℕ)) x) j) = (T ^ d) x := by
        show T ((T ^ (j : ℕ)) x) = (T ^ d) x
        rw [← Module.End.mul_apply, ← pow_succ', hj']
      rw [this]
      exact hTd
  have hinv : ∀ u ∈ Submodule.span (ZMod 2) S, T u ∈ Submodule.span (ZMod 2) S := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem y hy => exact hgen y hy
    | zero => rw [map_zero T]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add T y z]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy => rw [map_smul T a y]; exact Submodule.smul_mem _ _ hy
  have htop : Submodule.span (ZMod 2) S = ⊤ := by
    rcases hirr (Submodule.span (ZMod 2) S) hinv with h | h
    · exfalso
      have hxS : x ∈ Submodule.span (ZMod 2) S := by
        refine Submodule.subset_span ⟨⟨0, hdpos⟩, ?_⟩
        show (T ^ (0 : ℕ)) x = x
        rw [pow_zero]
        rfl
      rw [h, Submodule.mem_bot] at hxS
      exact hx hxS
    · exact h
  have hcard : Nat.card ↥S ≤ d := by
    have hsurj : Function.Surjective (fun j : Fin d => (⟨(T ^ (j : ℕ)) x, ⟨j, rfl⟩⟩ : ↥S)) := by
      rintro ⟨y, hy⟩
      obtain ⟨j, rfl⟩ := hy
      exact ⟨j, rfl⟩
    have h := Nat.card_le_card_of_surjective
      (fun j : Fin d => (⟨(T ^ (j : ℕ)) x, ⟨j, rfl⟩⟩ : ↥S)) hsurj
    rwa [Nat.card_fin] at h
  calc Module.finrank (ZMod 2) V
      = Module.finrank (ZMod 2) (Submodule.span (ZMod 2) S) := by
          rw [htop]
          exact (finrank_top (R := ZMod 2) (M := V)).symm
    _ ≤ S.toFinset.card := finrank_span_le_card S
    _ = Fintype.card ↥S := Set.toFinset_card S
    _ = Nat.card ↥S := (Nat.card_eq_fintype_card).symm
    _ ≤ d := hcard

/-- **The irreducible case is impossible.**  A finite `𝔽₂`-vector space of cardinality
`2 ^ (2 * n)` with an endomorphism `T` satisfying `T ^ (2 ^ n) = T` and having no proper
non-zero invariant subspace cannot exist. -/
theorem false_of_irreducible_pow_eq_self
    (T : V →ₗ[ZMod 2] V) {n : ℕ} (hn : 0 < n) (hT : T ^ 2 ^ n = T)
    (hirr : ∀ U : Submodule (ZMod 2) V, (∀ u ∈ U, T u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hcard : Nat.card V = 2 ^ (2 * n)) : False := by
  classical
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Nontrivial V := by
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, hcard]
    have h4 : (4 : ℕ) ≤ 2 ^ (2 * n) := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hfr : Module.finrank (ZMod 2) V = 2 * n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rw [Nat.card_zmod, hcard] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  have hm_dvd : minpoly (ZMod 2) T ∣ Polynomial.X ^ 2 ^ n - Polynomial.X := by
    refine minpoly.dvd (ZMod 2) T ?_
    rw [map_sub, map_pow (Polynomial.aeval T) Polynomial.X (2 ^ n), Polynomial.aeval_X, hT,
      sub_self]
  have hm_irred : Irreducible (minpoly (ZMod 2) T) := irreducible_minpoly_of_irreducible T hirr
  have hdeg_dvd : (minpoly (ZMod 2) T).natDegree ∣ n := by
    have h := Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X (k := ZMod 2) hm_irred
      (by simpa [Nat.card_zmod] using hm_dvd)
    simpa [Nat.card_zmod] using h
  have hle : Module.finrank (ZMod 2) V ≤ (minpoly (ZMod 2) T).natDegree :=
    finrank_le_natDegree_minpoly T hirr
  have hdle : (minpoly (ZMod 2) T).natDegree ≤ n :=
    Nat.le_of_dvd hn hdeg_dvd
  omega

end Crux

/-! ## Invariant complements (Maschke for an odd-order automorphism) -/

section Maschke

variable {V : Type} [AddCommGroup V] [AddExpTwo V] [Finite V]

/-- The only elements of `ZMod 2` are `0` and `1`. -/
theorem zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c; decide

/-- In an exponent-two group, `D • u = u` for odd `D`. -/
theorem odd_nsmul_eq {D : ℕ} (hD : Odd D) (u : V) : D • u = u := by
  obtain ⟨e, rfl⟩ := hD
  rw [show 2 * e + 1 = 1 + 2 * e from by ring, add_nsmul, one_nsmul,
    show (2 * e) • u = e • (2 • u) from by rw [mul_nsmul], two_nsmul, AddExpTwo.add_self,
    nsmul_zero, add_zero]

/-- **Invariant complements.**  If `D` is odd and `τ ^[D] = id`, then every `τ`-invariant
subgroup `U ≤ V` has a `τ`-invariant complement.  Averaging an arbitrary projection onto `U`
over the cyclic group generated by `τ` (of odd order `D`, so `1/D = 1` in characteristic two)
produces an equivariant projection whose kernel is the complement. -/
theorem exists_invariant_complement
    (τ : V ≃+ V) {D : ℕ} (hD : Odd D) (hτD : ∀ v : V, τ^[D] v = v)
    (U : AddSubgroup V) (hU : ∀ u : V, u ∈ U → τ u ∈ U) :
    ∃ U' : AddSubgroup V, (∀ u : V, u ∈ U' → τ u ∈ U') ∧
      (∀ v : V, ∃ u ∈ U, ∃ u' ∈ U', u + u' = v) ∧ U ⊓ U' = ⊥ := by
  classical
  letI : Module (ZMod 2) V :=
    AddCommGroup.zmodModule fun z => by rw [two_nsmul]; exact AddExpTwo.add_self z
  have hDpos : 0 < D := by obtain ⟨e, rfl⟩ := hD; omega
  -- `τ` as a linear map, and its inverse as `T ^ (D - 1)`
  let T : V →ₗ[ZMod 2] V := (τ.toAddMonoidHom).toZModLinearMap 2
  have hT : ∀ v : V, T v = τ v := fun v => rfl
  have hTiter : ∀ (k : ℕ) (v : V), (T ^ k) v = (T^[k]) v := by
    intro k
    induction k with
    | zero => intro v; rw [pow_zero, Function.iterate_zero_apply]; rfl
    | succ k ih =>
      intro v
      rw [pow_succ', Module.End.mul_apply, ih, Function.iterate_succ_apply', hT]
  have hTD : T ^ D = 1 := by
    ext v
    have h1 : (T ^ D) v = (T^[D]) v := hTiter D v
    have h2 : (T^[D]) v = (τ^[D]) v := rfl
    rw [h1, h2, hτD]
    rfl
  let Tinv : V →ₗ[ZMod 2] V := T ^ (D - 1)
  have hTinvinv : Tinv * T = 1 := by
    rw [show Tinv = T ^ (D - 1) from rfl, ← pow_succ, Nat.sub_add_cancel hDpos, hTD]
  have hTTinv : T * Tinv = 1 := by
    rw [show Tinv = T ^ (D - 1) from rfl, ← pow_succ' T (D - 1), Nat.sub_add_cancel hDpos, hTD]
  have hcommTT : Commute T Tinv := hTTinv.trans hTinvinv.symm
  have hmulpow : ∀ k : ℕ, (T ^ k) * (Tinv ^ k) = 1 := by
    intro k
    rw [(hcommTT.mul_pow k).symm, hTTinv, one_pow]
  have hTinvD : Tinv ^ D = 1 := by
    have h : Tinv = T ^ (D - 1) := rfl
    rw [h, ← pow_mul T (D - 1) D, show (D - 1) * D = D * (D - 1) from by ring,
      pow_mul T D (D - 1), hTD, one_pow]
  -- `U` as a submodule, invariant under `T` and `Tinv`
  let Us : Submodule (ZMod 2) V :=
    { carrier := U
      zero_mem' := U.zero_mem
      add_mem' := fun hx hy => U.add_mem hx hy
      smul_mem' := fun c x hx => by
        rcases zmod2_eq_zero_or_one c with rfl | rfl
        · rw [zero_smul]; exact U.zero_mem
        · rw [one_smul]; exact hx }
  have hTUs : ∀ u : V, u ∈ Us → T u ∈ Us := fun u hu => hU u hu
  have hTkUs : ∀ (k : ℕ), ∀ u : V, u ∈ Us → (T ^ k) u ∈ Us := by
    intro k
    induction k with
    | zero => intro u hu; rwa [pow_zero, Module.End.one_apply]
    | succ k ih =>
      intro u hu
      rw [pow_succ', Module.End.mul_apply]
      exact hTUs _ (ih u hu)
  have hTinvUs : ∀ u : V, u ∈ Us → Tinv u ∈ Us := by
    intro u hu
    rw [show Tinv = T ^ (D - 1) from rfl]
    exact hTkUs _ u hu
  have hTinvkUs : ∀ (k : ℕ), ∀ u : V, u ∈ Us → (Tinv ^ k) u ∈ Us := by
    intro k
    induction k with
    | zero => intro u hu; rwa [pow_zero, Module.End.one_apply]
    | succ k ih =>
      intro u hu
      rw [pow_succ', Module.End.mul_apply]
      exact hTinvUs _ (ih u hu)
  -- an arbitrary projection onto `U`
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl Us
  let π₀ : V →ₗ[ZMod 2] V := Us.projection W hW
  have hπ₀mem : ∀ v : V, π₀ v ∈ Us := by
    intro v
    have h := (Us.projectionOnto W hW v).2
    rwa [Submodule.coe_projectionOnto_apply (p := Us) (q := W) hW v] at h
  have hπ₀id : ∀ u : V, u ∈ Us → π₀ u = u := by
    intro u hu
    have h1 := Submodule.projectionOnto_apply_of_mem_left (p := Us) (q := W) hW hu
    have h2 := Submodule.coe_projectionOnto_apply (p := Us) (q := W) hW u
    rw [← h2, h1]
  -- the averaged projection
  let P : V →ₗ[ZMod 2] V := ∑ k ∈ Finset.range D, T ^ k * (π₀ * Tinv ^ k)
  have hPapply : ∀ v : V, P v = ∑ k ∈ Finset.range D, (T ^ k) (π₀ ((Tinv ^ k) v)) := by
    intro v
    rw [show P = ∑ k ∈ Finset.range D, T ^ k * (π₀ * Tinv ^ k) from rfl, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [Module.End.mul_apply, Module.End.mul_apply]
  have hPmem : ∀ v : V, P v ∈ Us := by
    intro v
    rw [hPapply]
    exact Submodule.sum_mem _ fun k _ => hTkUs _ _ (hπ₀mem _)
  have hPid : ∀ u : V, u ∈ Us → P u = u := by
    intro u hu
    have hterm : ∀ k ∈ Finset.range D, (T ^ k) (π₀ ((Tinv ^ k) u)) = u := by
      intro k _
      have h1 : (T ^ k) * (Tinv ^ k) = 1 := hmulpow k
      have h2 : (T ^ k) ((Tinv ^ k) u) = u := by
        rw [← Module.End.mul_apply, h1, Module.End.one_apply]
      rw [hπ₀id _ (hTinvkUs k u hu), h2]
    rw [hPapply, Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range]
    exact odd_nsmul_eq hD u
  -- `P` commutes with `T`
  have hstep : ∀ k : ℕ, T * (T ^ k * (π₀ * Tinv ^ k)) =
      (T ^ (k + 1) * (π₀ * Tinv ^ (k + 1))) * T := by
    intro k
    have h1 : Tinv ^ k * Tinv * T = Tinv ^ k := by rw [mul_assoc, hTinvinv, mul_one]
    calc T * (T ^ k * (π₀ * Tinv ^ k))
        = (T * T ^ k) * (π₀ * Tinv ^ k) := by rw [mul_assoc]
      _ = (T * T ^ k) * (π₀ * (Tinv ^ k * Tinv) * T) := by
            conv_rhs => rw [mul_assoc (π₀) (Tinv ^ k * Tinv) T, h1]
      _ = (T ^ (k + 1) * (π₀ * Tinv ^ (k + 1))) * T := by
            rw [← pow_succ' T k, ← pow_succ Tinv k, ← mul_assoc]
  have hshift : ∑ k ∈ Finset.range D, (T ^ (k + 1) * (π₀ * Tinv ^ (k + 1))) =
      ∑ k ∈ Finset.range D, (T ^ k * (π₀ * Tinv ^ k)) := by
    have hgD : T ^ D * (π₀ * Tinv ^ D) = T ^ 0 * (π₀ * Tinv ^ 0) := by
      rw [hTD, hTinvD]; simp
    have h1 : ∑ k ∈ Finset.range D, (T ^ (k + 1) * (π₀ * Tinv ^ (k + 1))) =
        (∑ k ∈ Finset.range (D - 1), (T ^ (k + 1) * (π₀ * Tinv ^ (k + 1)))) +
          T ^ 0 * (π₀ * Tinv ^ 0) := by
      rw [show Finset.range D = Finset.range ((D - 1) + 1) from by
        rw [Nat.sub_add_cancel hDpos]]
      rw [Finset.sum_range_succ, Nat.sub_add_cancel hDpos, hgD]
    have h2 : ∑ k ∈ Finset.range D, (T ^ k * (π₀ * Tinv ^ k)) =
        (∑ k ∈ Finset.range (D - 1), (T ^ (k + 1) * (π₀ * Tinv ^ (k + 1)))) +
          T ^ 0 * (π₀ * Tinv ^ 0) := by
      rw [show Finset.range D = Finset.range ((D - 1) + 1) from by
        rw [Nat.sub_add_cancel hDpos]]
      rw [Finset.sum_range_succ', add_comm]
    rw [h1, h2]
  have hPT : P * T = T * P := by
    have hPexp : P = ∑ k ∈ Finset.range D, T ^ k * (π₀ * Tinv ^ k) := rfl
    have hcalc : T * P = P * T := by
      calc T * P
          = T * (∑ k ∈ Finset.range D, T ^ k * (π₀ * Tinv ^ k)) := by rw [hPexp]
        _ = ∑ k ∈ Finset.range D, T * (T ^ k * (π₀ * Tinv ^ k)) := by rw [Finset.mul_sum]
        _ = ∑ k ∈ Finset.range D, (T ^ (k + 1) * (π₀ * Tinv ^ (k + 1))) * T :=
              Finset.sum_congr rfl fun k _ => hstep k
        _ = (∑ k ∈ Finset.range D, (T ^ (k + 1) * (π₀ * Tinv ^ (k + 1)))) * T := by
              rw [Finset.sum_mul]
        _ = (∑ k ∈ Finset.range D, (T ^ k * (π₀ * Tinv ^ k))) * T := by rw [hshift]
        _ = P * T := by rw [hPexp]
    exact hcalc.symm
  -- the complement
  refine ⟨(LinearMap.ker P).toAddSubgroup, ?_, ?_, ?_⟩
  · intro u hu
    rw [Submodule.mem_toAddSubgroup, LinearMap.mem_ker] at hu ⊢
    rw [← hT u]
    have h1 : P (T u) = T (P u) := by
      have h := congrArg (fun (ψ : Module.End (ZMod 2) V) => ψ u) hPT
      rw [Module.End.mul_apply, Module.End.mul_apply] at h
      exact h
    rw [h1, hu, map_zero T]
  · intro v
    refine ⟨P v, hPmem v, v + P v, ?_, ?_⟩
    · rw [Submodule.mem_toAddSubgroup, LinearMap.mem_ker, map_add, hPid _ (hPmem v)]
      rw [two_add_self]
    · rw [← add_assoc, add_comm (P v) v, add_assoc, two_add_self, add_zero]
  · refine le_antisymm ?_ bot_le
    intro x hx
    rw [AddSubgroup.mem_inf] at hx
    obtain ⟨hxU, hxker⟩ := hx
    rw [Submodule.mem_toAddSubgroup, LinearMap.mem_ker] at hxker
    rw [← hPid x hxU, hxker]
    exact (⊥ : AddSubgroup V).zero_mem

end Maschke

/-! ## The `q2XiV`-specific ingredients -/

variable {V W : Type} [AddCommGroup V] [AddExpTwo V] [AddCommGroup W] [AddExpTwo W]
variable [Finite V] [Finite W] {b : V → V → W} [Biadd b]

/-- **Divisibility of `|U| - 1` for a `q2XiV`-invariant subgroup.** -/
theorem dvd_card_sub_one_of_q2XiV_invariant
    (hcardV : Nat.card V = Nat.card W ^ 2) (hW : 4 ≤ Nat.card W)
    (hinvol : ∀ x : TwoStep V W b, x ^ 2 = 1 → x ∈ Subgroup.center (TwoStep V W b))
    (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b)) (hord : orderOf ξ = Nat.card W - 1)
    (htrans : ∀ x y : TwoStep V W b, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ξ ^ k) x = y)
    (U : AddSubgroup V) (hU : U ≠ ⊥)
    (hinv : ∀ u : V, u ∈ U → q2XiV hcenter ξ u ∈ U) :
    (Nat.card W - 1) ∣ (Nat.card ↥U - 1) := by
  classical
  obtain ⟨u, huU, hu0⟩ : ∃ u : V, u ∈ U ∧ u ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    refine hU (le_antisymm ?_ bot_le)
    intro y hy
    rw [hcon y hy]
    exact zero_mem (⊥ : AddSubgroup V)
  set S : Set V := {x : V | x ∈ U ∧ x ≠ 0} with hSdef
  have hSinv : ∀ x ∈ S, q2XiVPerm hcenter ξ x ∈ S := by
    rintro x ⟨hxU, hx0⟩
    have hx' : q2XiVPerm hcenter ξ x = q2XiV hcenter ξ x := q2XiVPerm_apply hcenter ξ x
    rw [hx']
    exact ⟨hinv x hxU, fun h => hx0 ((q2XiV hcenter ξ).injective (by rw [h, map_zero]))⟩
  have hfree : ∀ k : ℕ, ∀ x ∈ S, (q2XiVPerm hcenter ξ ^ k) x = x → q2XiVPerm hcenter ξ ^ k = 1 :=
    fun k x hx h => q2XiVPerm_pow_eq_one_of_fix hcenter ξ hinvol hW hord htrans hx.2 h
  have hdvd := orderOf_dvd_ncard_of_semiregular (q2XiVPerm hcenter ξ) S hSinv hfree
  rw [orderOf_q2XiVPerm hcenter ξ hinvol hW hord htrans hcardV] at hdvd
  have hSncard : S.ncard = Nat.card ↥U - 1 := by
    rw [hSdef, ← Nat.card_coe_set_eq]
    have hcard : Nat.card {x : V // x ∈ U ∧ x ≠ 0} = Nat.card {x : ↥U // x ≠ 0} :=
      Nat.card_congr
        { toFun := fun x => ⟨⟨x.1, x.2.1⟩,
              fun h => x.2.2 (show x.1 = 0 from congrArg Subtype.val h)⟩
          invFun := fun x => ⟨x.1.1, x.1.2,
              fun h => x.2 (show x.1 = 0 from Subtype.ext h)⟩
          left_inv := fun x => rfl
          right_inv := fun x => rfl }
    show Nat.card {x : V // x ∈ U ∧ x ≠ 0} = Nat.card ↥U - 1
    rw [hcard, card_subtype_ne_zero ↥U 0]
  rw [hSncard] at hdvd
  exact hdvd

/-- **Transitivity on a `q2XiV`-invariant subgroup of order `|W|`.** -/
theorem exists_iterate_eq_of_card_eq_q2XiV
    (hW : 4 ≤ Nat.card W)
    (hinvol : ∀ x : TwoStep V W b, x ^ 2 = 1 → x ∈ Subgroup.center (TwoStep V W b))
    (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b)) (hord : orderOf ξ = Nat.card W - 1)
    (htrans : ∀ x y : TwoStep V W b, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ξ ^ k) x = y)
    (U : AddSubgroup V) (hU : ∀ u : V, u ∈ U → q2XiV hcenter ξ u ∈ U)
    (hcard : Nat.card ↥U = Nat.card W)
    (u : V) (hu : u ∈ U) (hu0 : u ≠ 0) (v : V) (hv : v ∈ U) (hv0 : v ≠ 0) :
    ∃ k : ℕ, ((q2XiV hcenter ξ : V → V)^[k]) u = v := by
  classical
  have hmem : ∀ k : ℕ, ((q2XiV hcenter ξ : V → V)^[k]) u ∈ U := by
    intro k
    induction k with
    | zero => rw [Function.iterate_zero_apply]; exact hu
    | succ k ih => rw [Function.iterate_succ_apply']; exact hU _ ih
  have hzero : ∀ k : ℕ, ((q2XiV hcenter ξ : V → V)^[k]) (0 : V) = 0 := by
    intro k
    induction k with
    | zero => rw [Function.iterate_zero_apply]
    | succ k ih => rw [Function.iterate_succ_apply', ih]; exact map_zero _
  have hne : ∀ k : ℕ, ((q2XiV hcenter ξ : V → V)^[k]) u ≠ 0 := by
    intro k hk0
    refine hu0 ((q2XiV hcenter ξ).injective.iterate k ?_)
    rw [hk0, hzero k]
  let g : Fin (Nat.card W - 1) → {x : ↥U // x ≠ 0} :=
    fun k => ⟨⟨((q2XiV hcenter ξ : V → V)^[(k : ℕ)]) u, hmem k⟩,
      fun h => hne k (congrArg (fun y : ↥U => (y : V)) h)⟩
  have hgval : ∀ k : Fin (Nat.card W - 1),
      ((g k : ↥U) : V) = ((q2XiV hcenter ξ : V → V)^[(k : ℕ)]) u := fun _ => rfl
  have hg : Function.Injective g := by
    have hstep : ∀ i j : Fin (Nat.card W - 1), (i : ℕ) ≤ (j : ℕ) →
        ((q2XiV hcenter ξ : V → V)^[(i : ℕ)]) u =
          ((q2XiV hcenter ξ : V → V)^[(j : ℕ)]) u → i = j := by
      intro i j hle heq
      have hfix : ((q2XiV hcenter ξ : V → V)^[((j : ℕ) - (i : ℕ))]) u = u := by
        have h3 := Function.iterate_add_apply (q2XiV hcenter ξ : V → V) (i : ℕ) ((j : ℕ) - (i : ℕ)) u
        rw [Nat.add_sub_of_le hle] at h3
        have h4 : ((q2XiV hcenter ξ : V → V)^[(i : ℕ)])
            (((q2XiV hcenter ξ : V → V)^[((j : ℕ) - (i : ℕ))]) u)
            = ((q2XiV hcenter ξ : V → V)^[(i : ℕ)]) u := h3.symm.trans heq.symm
        exact (q2XiV hcenter ξ).injective.iterate (i : ℕ) h4
      have hdvd : (Nat.card W - 1) ∣ ((j : ℕ) - (i : ℕ)) :=
        q2XiV_fix_dvd hcenter ξ hinvol hW hord htrans u hu0 _ hfix
      have hlt : (j : ℕ) - (i : ℕ) < Nat.card W - 1 :=
        lt_of_le_of_lt (Nat.sub_le _ _) j.isLt
      have h0 : (j : ℕ) - (i : ℕ) = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
      exact Fin.ext (by omega)
    intro i j hij
    have h1 : ((q2XiV hcenter ξ : V → V)^[(i : ℕ)]) u =
        ((q2XiV hcenter ξ : V → V)^[(j : ℕ)]) u :=
      (hgval i).symm.trans
        ((congrArg (fun y : {x : ↥U // x ≠ 0} => ((y : ↥U) : V)) hij).trans (hgval j))
    rcases le_total (i : ℕ) (j : ℕ) with hle | hle
    · exact hstep i j hle h1
    · exact (hstep j i hle h1.symm).symm
  haveI : Fintype ↥U := Fintype.ofFinite ↥U
  haveI : Fintype {x : ↥U // x ≠ 0} := Fintype.ofFinite _
  have hcardD : Fintype.card {x : ↥U // x ≠ 0} = Nat.card W - 1 := by
    have h1 : Nat.card {x : ↥U // x ≠ 0} = Nat.card W - 1 := by
      rw [card_subtype_ne_zero ↥U (0 : ↥U), hcard]
    exact (Nat.card_eq_fintype_card (α := {x : ↥U // x ≠ 0})).symm.trans h1
  have hbij : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).mpr
      ⟨hg, by rw [hcardD, Fintype.card_fin]⟩
  obtain ⟨k, hk⟩ := hbij.2
    (⟨⟨v, hv⟩, fun h => hv0 (congrArg (fun y : ↥U => (y : V)) h)⟩ : {x : ↥U // x ≠ 0})
  have hgv : ((g k : ↥U) : V) = v :=
    congrArg (fun y : {x : ↥U // x ≠ 0} => ((y : ↥U) : V)) hk
  exact ⟨(k : ℕ), by rw [← hgval k]; exact hgv⟩

/-! ## The target -/

/-- **The `ξ`-eigen-decomposition of `V`** (first step of Higman's Lemma 12 for the order-`q³`
two-step groups, `q = |W|`).  If `ξ` is a regular automorphism of `TwoStep V W b` (order
`q - 1 = |W| - 1`, the number of involutions) then `V` is the sum of two `ξ`-invariant subgroups
of order `q`, on each of which `ξ` is transitive on the non-zero elements.

Ingredients already in the workspace: `V` is a semisimple `𝔽₂[ξ]`-module (`ξ` has odd order, so
Maschke applies); every non-zero `ξ`-invariant `U` inside `V` satisfies `|U| ≥ |W|`
(`Work.Higman.card_kerFst_sq_le_card`, applied to the lift of `U` to `TwoStep V W b`); and
`|V| = |W|²`.  The hypothesis `orderOf ξ = |W| - 1` rules out the case of a single irreducible
constituent `V` of order `|W|²` (an element of order dividing `2ⁿ - 1` inside a field of degree
`2n` lies in the subfield of degree `n`).  Transitivity on `U ∖ {0}` uses the `ξ`-equivariance
`b (ξu) (ξu) = ξ (b u u)` of the squaring form together with the transitivity of `ξ` on the
involutions (so that its action on `W ∖ {0}` is a Singer cycle).

The same conclusion with `ζ` in place of `ξ` and `Work.Higman.Q3.xiV` in place of
`Work.Higman.q2XiV` is stated (with `sorry`) in `Submission.Work.Higman.Q3.exists_invariant_decomposition`;
this version avoids that module's import of `Submission.Work.Higman.Q3.induced`. -/
theorem exists_xi_decomposition
    {V W : Type} [AddCommGroup V] [AddExpTwo V] [AddCommGroup W] [AddExpTwo W]
    [Finite V] [Finite W]
    {b : V → V → W} [Biadd b]
    (hcardV : Nat.card V = Nat.card W ^ 2) (hW : 4 ≤ Nat.card W)
    (hinvol : ∀ x : TwoStep V W b, x ^ 2 = 1 → x ∈ Subgroup.center (TwoStep V W b))
    (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b)) (hord : orderOf ξ = Nat.card W - 1)
    (htrans : ∀ x y : TwoStep V W b, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ξ ^ k) x = y) :
    ∃ U U' : AddSubgroup V,
      (∀ v : V, v ∈ U → q2XiV hcenter ξ v ∈ U) ∧
      (∀ v : V, v ∈ U' → q2XiV hcenter ξ v ∈ U') ∧
      (∀ v : V, ∃ u ∈ U, ∃ u' ∈ U', u + u' = v) ∧
      (U ⊓ U' = ⊥) ∧
      Nat.card ↥U = Nat.card W ∧ Nat.card ↥U' = Nat.card W ∧
      (∀ u : V, u ∈ U → u ≠ 0 → ∀ v : V, v ∈ U → v ≠ 0 →
        ∃ k : ℕ, ((q2XiV hcenter ξ : V → V)^[k]) u = v) ∧
      (∀ u : V, u ∈ U' → u ≠ 0 → ∀ v : V, v ∈ U' → v ≠ 0 →
        ∃ k : ℕ, ((q2XiV hcenter ξ : V → V)^[k]) u = v) := by
  classical
  obtain ⟨n, hn⟩ := card_W_eq_two_pow (W := W) hW
  have hnpos : 0 < n := by
    by_contra h
    push_neg at h
    have : Nat.card W ≤ 1 := by
      calc Nat.card W = 2 ^ n := hn
        _ ≤ 2 ^ 0 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 1 := by norm_num
    omega
  have hVcard : Nat.card V = 2 ^ (2 * n) := by
    rw [hcardV, hn, ← pow_mul, Nat.mul_comm n 2]
  letI : Module (ZMod 2) V :=
    AddCommGroup.zmodModule fun z => by rw [two_nsmul]; exact AddExpTwo.add_self z
  letI : Module (ZMod 2) W :=
    AddCommGroup.zmodModule fun z => by rw [two_nsmul]; exact AddExpTwo.add_self z
  let T : V →ₗ[ZMod 2] V := (q2XiV hcenter ξ).toAddMonoidHom.toZModLinearMap 2
  have hT : ∀ v : V, T v = q2XiV hcenter ξ v := fun v => rfl
  have hTiter : ∀ (k : ℕ) (v : V), (T ^ k) v = ((q2XiV hcenter ξ : V → V)^[k]) v := by
    intro k
    induction k with
    | zero => intro v; rw [pow_zero, Function.iterate_zero_apply]; rfl
    | succ k ih =>
      intro v
      rw [pow_succ', Module.End.mul_apply, ih, Function.iterate_succ_apply', hT]
  have hξW : ξ ^ 2 ^ n = ξ := by
    rw [← hn]
    have hWpos : 0 < Nat.card W := by omega
    rw [show Nat.card W = Nat.card W - 1 + 1 from (Nat.sub_add_cancel hWpos).symm, pow_succ,
      show ξ ^ (Nat.card W - 1) = 1 from by rw [← hord]; exact pow_orderOf_eq_one ξ, one_mul]
  have hTpow : T ^ 2 ^ n = T := by
    ext v
    rw [hTiter, ← q2XiV_pow hcenter ξ (2 ^ n) v, hξW, hT]
  by_cases hex : ∃ U : AddSubgroup V, U ≠ ⊥ ∧ U ≠ ⊤ ∧ (∀ u : V, u ∈ U → q2XiV hcenter ξ u ∈ U)
  · obtain ⟨U, hUbot, hUtop, hUinv⟩ := hex
    have hdiv :=
      dvd_card_sub_one_of_q2XiV_invariant hcardV hW hinvol hcenter ξ hord htrans U hUbot hUinv
    haveI : AddExpTwo ↥U := ⟨fun x => Subtype.ext (by simpa using AddExpTwo.add_self x.1)⟩
    haveI : Module (ZMod 2) ↥U :=
      AddCommGroup.zmodModule fun z => by rw [two_nsmul]; exact AddExpTwo.add_self z
    haveI : Module.Finite (ZMod 2) ↥U := Module.Finite.of_finite
    have hcardU : Nat.card ↥U = 2 ^ Module.finrank (ZMod 2) ↥U := by
      have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥U)
      rwa [Nat.card_zmod] at h
    have hdvd : n ∣ Module.finrank (ZMod 2) ↥U := by
      rw [hcardU, hn] at hdiv
      exact (pow_sub_one_dvd_pow_sub_one_iff (x := 2) (by norm_num) hnpos).mp hdiv
    have hnU : 0 < Module.finrank (ZMod 2) ↥U := by
      have hnt : Nontrivial ↥U := by
        obtain ⟨u, hu, hu0⟩ : ∃ u : V, u ∈ U ∧ u ≠ 0 := by
          by_contra hcon
          push_neg at hcon
          exact hUbot (le_antisymm (fun y hy => by
            rw [hcon y hy]; exact zero_mem (⊥ : AddSubgroup V)) bot_le)
        exact ⟨⟨u, hu⟩, ⟨0, U.zero_mem⟩, fun h => hu0 (congrArg Subtype.val h)⟩
      exact Module.finrank_pos_iff.mpr hnt
    have hle : Module.finrank (ZMod 2) ↥U ≤ 2 * n := by
      have h1 : Nat.card ↥U ≤ Nat.card V := Nat.card_le_card_of_injective _ Subtype.val_injective
      rw [hcardU, hVcard] at h1
      have h2 : Module.finrank (ZMod 2) ↥U ≤ 2 * n := by
        by_contra hc
        push_neg at hc
        exact absurd h1 (not_le.mpr (Nat.pow_lt_pow_right (by norm_num) hc))
      exact h2
    have hfin : Module.finrank (ZMod 2) ↥U = n := by
      obtain ⟨k, hk⟩ := hdvd
      have hk2 : k ≤ 2 := by
        have h2 : n * k ≤ n * 2 := by
          calc n * k = Module.finrank (ZMod 2) ↥U := hk.symm
            _ ≤ 2 * n := hle
            _ = n * 2 := by ring
        exact Nat.le_of_mul_le_mul_left h2 hnpos
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · rw [h, mul_zero] at hk
          omega
        · exact h
      interval_cases k
      · simpa using hk
      · exfalso
        apply hUtop
        have htopcard : Nat.card ↥(⊤ : AddSubgroup V) = 2 ^ (2 * n) :=
          (Nat.card_congr (AddSubgroup.topEquiv (G := V)).toEquiv).trans hVcard
        have hcard2 : Nat.card ↥U = Nat.card ↥(⊤ : AddSubgroup V) := by
          rw [hcardU, hk, htopcard, Nat.mul_comm n 2]
        exact AddSubgroup.eq_of_le_of_card_ge le_top (le_of_eq hcard2.symm)
    have hcardW : Nat.card ↥U = Nat.card W := by rw [hcardU, hfin, hn]
    have hWodd : Odd (Nat.card W - 1) := by
      rw [hn]
      obtain ⟨m, hm⟩ : ∃ m, 2 ^ n = 2 * m :=
        ⟨2 ^ (n - 1), by rw [← pow_succ', Nat.sub_add_cancel hnpos]⟩
      exact ⟨m - 1, by omega⟩
    have hfixD : ∀ v : V, (q2XiV hcenter ξ)^[Nat.card W - 1] v = v := by
      intro v
      rw [← q2XiV_pow hcenter ξ (Nat.card W - 1) v, ← hord, pow_orderOf_eq_one, q2XiV_apply]
      rfl
    obtain ⟨U', hU'inv, hU'sum, hU'disj⟩ :=
      exists_invariant_complement (q2XiV hcenter ξ) (D := Nat.card W - 1) hWodd hfixD U hUinv
    have hcardU' : Nat.card ↥U' = Nat.card W := by
      have hbij : Function.Bijective (fun p : ↥U × ↥U' => (p.1 : V) + (p.2 : V)) := by
        constructor
        · rintro ⟨u₁, u₁'⟩ ⟨u₂, u₂'⟩ heq
          have heq' : (u₁ : V) + u₁' = (u₂ : V) + u₂' := heq
          have hkey : (u₁ : V) + u₂ = u₁' + u₂' := by
            have h := congrArg (fun t : V => t + ((u₂ : V) + u₁')) heq'
            have hl : ((u₁ : V) + u₁') + ((u₂ : V) + u₁') = (u₁ : V) + u₂ := by
              rw [show ((u₁ : V) + u₁') + ((u₂ : V) + u₁') =
                  ((u₁ : V) + u₂) + (u₁' + u₁') from by abel,
                AddExpTwo.add_self (u₁' : V), add_zero]
            have hr : ((u₂ : V) + u₂') + ((u₂ : V) + u₁') = u₁' + u₂' := by
              rw [show ((u₂ : V) + u₂') + ((u₂ : V) + u₁') =
                  (u₁' + u₂') + (u₂ + u₂) from by abel,
                AddExpTwo.add_self (u₂ : V), add_zero]
            rw [hl, hr] at h
            exact h
          have hbot : (u₁ : V) + u₂ ∈ (⊥ : AddSubgroup V) := by
            rw [← hU'disj, AddSubgroup.mem_inf]
            exact ⟨U.add_mem u₁.2 u₂.2, by rw [hkey]; exact U'.add_mem u₁'.2 u₂'.2⟩
          rw [AddSubgroup.mem_bot] at hbot
          have h12 : (u₁ : V) = u₂ := by
            calc (u₁ : V) = (u₁ : V) + 0 := (add_zero _).symm
              _ = (u₁ : V) + (u₂ + u₂) := by rw [AddExpTwo.add_self (u₂ : V)]
              _ = ((u₁ : V) + u₂) + u₂ := by rw [add_assoc]
              _ = 0 + u₂ := by rw [hbot]
              _ = u₂ := zero_add _
          have h1' : u₁' = u₂' := by
            have h2 : (u₂ : V) + u₁' = (u₂ : V) + u₂' := by
              rw [h12] at heq'
              exact heq'
            exact Subtype.ext (add_left_cancel h2)
          rw [Subtype.ext h12, h1']
        · rintro v
          obtain ⟨u, hu, u', hu', huv⟩ := hU'sum v
          exact ⟨(⟨u, hu⟩, ⟨u', hu'⟩), huv⟩
      have h1 : Nat.card (↥U × ↥U') = Nat.card V :=
        Nat.card_congr (Equiv.ofBijective _ hbij)
      rw [Nat.card_prod, hcardW, hcardV, pow_two] at h1
      exact Nat.mul_left_cancel (by omega : 0 < Nat.card W) h1
    refine ⟨U, U', hUinv, hU'inv, hU'sum, hU'disj, hcardW, hcardU', ?_, ?_⟩
    · intro u hu hu0 v hv hv0
      exact exists_iterate_eq_of_card_eq_q2XiV hW hinvol hcenter ξ hord htrans U hUinv hcardW
        u hu hu0 v hv hv0
    · intro u hu hu0 v hv hv0
      exact exists_iterate_eq_of_card_eq_q2XiV hW hinvol hcenter ξ hord htrans U' hU'inv hcardU'
        u hu hu0 v hv hv0
  · exfalso
    rw [not_exists] at hex
    have hirr : ∀ U : Submodule (ZMod 2) V, (∀ u ∈ U, T u ∈ U) → U = ⊥ ∨ U = ⊤ := by
      intro U hU
      have hU' : ∀ u : V, u ∈ U.toAddSubgroup → q2XiV hcenter ξ u ∈ U.toAddSubgroup := by
        intro u hu
        rw [Submodule.mem_toAddSubgroup] at hu ⊢
        rw [← hT u]
        exact hU u hu
      rcases eq_or_ne U.toAddSubgroup ⊥ with hbot | hbot
      · left
        refine (Submodule.toAddSubgroup_inj U (⊥ : Submodule (ZMod 2) V)).mp ?_
        rw [hbot, Submodule.bot_toAddSubgroup]
      rcases eq_or_ne U.toAddSubgroup ⊤ with htop | htop
      · right
        refine (Submodule.toAddSubgroup_inj U (⊤ : Submodule (ZMod 2) V)).mp ?_
        rw [htop, Submodule.top_toAddSubgroup]
      · exact absurd ⟨hbot, htop, hU'⟩ (hex U.toAddSubgroup)
    exact false_of_irreducible_pow_eq_self T hnpos hTpow hirr hVcard

end Work.Higman.Q3.L12
