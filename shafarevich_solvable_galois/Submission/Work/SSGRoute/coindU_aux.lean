/-
Auxiliary results for `Work.SSGRoute.coindU_H1_subsingleton`.

The target is `Subsingleton (H¹(Gal(Ω/k), Maps(Gal(K/k), Ωˣ)))` for `K/k` finite Galois and `Ω` an
algebraic closure of `k`.  The proof is Shapiro's lemma together with Hilbert 90 for the subgroup
`Gal(Ω/K) ≤ Gal(Ω/k)`; the pieces gathered here are:

* `fixedField_expChar_pow` — the fixed field of `Aut(Ω/M)` is the relative perfect closure of `M`
  (Artin's theorem in the inseparable case, in the `p`-power form, and valid in all
  characteristics since `ringExpChar` is `1` in characteristic zero);
* `exists_fixingSubgroup_subset`, `locconst_fixingSubgroupEquiv_symm` — the subspace topology on
  the fixing subgroup of a finite subextension is the Krull topology of that subextension, so
  local constancy is preserved by the identification;
* `expChar_pow_eq_one` — `p`-power roots of unity are trivial in characteristic `p`;
* `hilbert90_isAlgClosure` — **Hilbert 90 for the absolute Galois group** of a field `k`: every
  locally constant crossed homomorphism `Gal(Ω/k) → Ωˣ` is a coboundary, for *any* field `k` (in
  particular in characteristic `p`, where `Ω/k` need not be separable);
* `exists_div_fixingSubgroup` — the same statement for the fixing subgroup of a finite
  intermediate field, which is the input to Shapiro's lemma.

## Note on the shared dependency

This file (and the target `coindU_H1_subsingleton`) imports
`Submission/Work/SSGRoute/ext_h1_bridge.lean`, the shared file defining `CoindU`, `res` and `umap`.
That file had been left in a non-compiling state by another agent: the proof of
`Work.SSGRoute.isDiscreteModule_pi_coindU` used `rfl` where the coherence lemma `one_smul` is
required, so the whole import chain failed to build.  That single tactic has been repaired
(`rfl` → `one_smul _ _`); no statement, definition or other proof was touched, and a copy of the
file as found is kept at `_dep_backup_ext_h1_bridge_A.lean` in the workspace root.
-/
import Mathlib
import Submission.Work.SSGRoute.homCoindDefs
import Submission.Work.AbsoluteKummer.All
import Submission.Work.SSGRoute.isOpen_map_fixingSubgroupEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical Topology
open Polynomial Filter

namespace Work.SSGRoute

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]

/-! ## The fixed field of the automorphism group -/

/-- **Artin's theorem, inseparable case.** If `x` is fixed by every `k`-automorphism of the
algebraic closure `Ω` that fixes an intermediate field `M` pointwise, then some
`ringExpChar`-power of `x` lies in `M`.  In characteristic `0` (`ringExpChar Ω = 1`) this says
`x ∈ M`; in characteristic `p` it says that `x` is purely inseparable over `M`. -/
theorem fixedField_expChar_pow [IsAlgClosure k Ω] {M : IntermediateField k Ω} (x : Ω)
    (hx : ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ M.fixingSubgroup → σ x = x) :
    ∃ n : ℕ, x ^ (ringExpChar Ω ^ n) ∈ M := by
  have hAlgClosed : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have : IsAlgClosed Ω := hAlgClosed
  have hAlg : Algebra.IsAlgebraic ↥M Ω := inferInstance
  -- every root of the minimal polynomial of `x` over `M` in `Ω` is `x` itself
  have hroot : ∀ y : Ω, Polynomial.aeval y (minpoly ↥M x) = 0 → y = x := by
    intro y hy
    obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval
      (F := ↥M) (E := Ω) (K := Ω)
      (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) hy
    have hbij : Function.Bijective φ := Algebra.IsAlgebraic.algHom_bijective φ
    let σ : Ω ≃ₐ[↥M] Ω := AlgEquiv.ofBijective φ hbij
    have hσx : σ x = y := hφ
    have hfix : (((IntermediateField.fixingSubgroupEquiv M).symm σ : Ω ≃ₐ[k] Ω)) x = x :=
      hx _ (Subtype.mem _)
    rw [← hσx]
    exact hfix
  have hnat : (minpoly ↥M x).natSepDegree = 1 := by
    rw [Polynomial.natSepDegree_eq_of_splits (minpoly ↥M x) (E := Ω) (IsAlgClosed.splits _)]
    have hone : ((minpoly ↥M x).aroots Ω).toFinset = {x} := by
      ext y
      rw [Multiset.mem_toFinset, Finset.mem_singleton, Polynomial.mem_aroots]
      constructor
      · rintro ⟨hne, hy⟩
        exact hroot y hy
      · intro hy
        rw [hy]
        exact ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral x),
          by rw [minpoly.aeval]⟩
    rw [hone, Finset.card_singleton]
  have hpc : x ∈ perfectClosure ↥M Ω := by
    rw [mem_perfectClosure_iff_natSepDegree_eq_one]
    exact hnat
  rw [mem_perfectClosure_iff] at hpc
  obtain ⟨n, hn⟩ := hpc
  refine ⟨n, ?_⟩
  have hrc : ringExpChar ↥M = ringExpChar Ω := by
    rw [show ringExpChar ↥M = max (ringChar ↥M) 1 from rfl,
      show ringExpChar Ω = max (ringChar Ω) 1 from rfl, Algebra.ringChar_eq (K := ↥M) (L := Ω)]
  rw [hrc] at hn
  obtain ⟨m, hm⟩ := hn
  rw [← hm]
  exact m.2

/-! ## Comparing the topology on the fixing subgroup with the Krull topology -/

/-- Every neighbourhood of `1` in the fixing subgroup of a finite intermediate field `K` contains
the fixing subgroup of a finite intermediate field containing `K`. -/
theorem exists_fixingSubgroup_subset {K : IntermediateField k Ω} [FiniteDimensional k K]
    {V : Set ↥(K.fixingSubgroup)} (hV : IsOpen V) (h1 : 1 ∈ V) :
    ∃ M : IntermediateField k Ω, FiniteDimensional k M ∧ K ≤ M ∧
      ∀ x : ↥(K.fixingSubgroup), (x : Ω ≃ₐ[k] Ω) ∈ M.fixingSubgroup → x ∈ V := by
  obtain ⟨V', hV'open, hV'eq⟩ := isOpen_induced_iff.mp hV
  have h1' : (1 : Ω ≃ₐ[k] Ω) ∈ V' := by
    have h2 : (1 : ↥(K.fixingSubgroup)) ∈ Subtype.val ⁻¹' V' := by rw [hV'eq]; exact h1
    simpa using h2
  obtain ⟨E, _, hEsub⟩ :=
    (krullTopology_mem_nhds_one_iff k Ω V').mp (hV'open.mem_nhds h1')
  refine ⟨E ⊔ K, inferInstance, le_sup_right, fun x hx => ?_⟩
  have hx' : x ∈ Subtype.val ⁻¹' V' :=
    hEsub (IntermediateField.fixingSubgroup_antitone le_sup_left hx)
  rw [hV'eq] at hx'
  exact hx'

/-- **Local constancy transfers across the Galois correspondence.**  The isomorphism
`K.fixingSubgroup ≃* Gal(Ω/↥K)` is a homeomorphism for the subspace Krull topology on the left and
the Krull topology on the right, so pulling back a locally constant function along the inverse is
locally constant. -/
theorem locconst_fixingSubgroupEquiv_symm {K : IntermediateField k Ω} [FiniteDimensional k K]
    {N : Type*} [AddCommGroup N] [DistribMulAction (Ω ≃ₐ[k] Ω) N]
    {f : ↥(K.fixingSubgroup) → N}
    (hf : Work.AbsoluteKummer.IsLocallyConstant f) :
    Work.AbsoluteKummer.IsLocallyConstant
      (fun σ : Ω ≃ₐ[K] Ω => f ((IntermediateField.fixingSubgroupEquiv K).symm σ)) := by
  intro σ₀
  set e := IntermediateField.fixingSubgroupEquiv K with he
  obtain ⟨U, hUopen, hσ₀U, hUc⟩ := hf (e.symm σ₀)
  set V : Set ↥(K.fixingSubgroup) := {x | e.symm σ₀ * x ∈ U} with hVdef
  have hVopen : IsOpen V := hUopen.preimage (continuous_const.mul continuous_id)
  have h1V : (1 : ↥(K.fixingSubgroup)) ∈ V := by
    change e.symm σ₀ * 1 ∈ U
    rw [mul_one]
    exact hσ₀U
  obtain ⟨M, hMfin, hKle, hMV⟩ := exists_fixingSubgroup_subset (K := K) hVopen h1V
  let H' : Subgroup ↥(K.fixingSubgroup) := M.fixingSubgroup.comap (Subgroup.subtype _)
  have hH'open : IsOpen (H' : Set ↥(K.fixingSubgroup)) :=
    (IntermediateField.fixingSubgroup_isOpen M).preimage continuous_subtype_val
  have himg : IsOpen ((H'.map e.toMonoidHom : Subgroup (Ω ≃ₐ[K] Ω)) : Set (Ω ≃ₐ[K] Ω)) :=
    isOpen_map_fixingSubgroupEquiv K H' hH'open
  refine ⟨(fun ρ : Ω ≃ₐ[K] Ω => σ₀⁻¹ * ρ) ⁻¹' (H'.map e.toMonoidHom : Set (Ω ≃ₐ[K] Ω)),
    himg.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp only [Set.mem_preimage, inv_mul_cancel]
    exact Subgroup.one_mem _
  · intro ρ hρ
    have hρ' : e.symm (σ₀⁻¹ * ρ) ∈ H' := by
      obtain ⟨x, hx, hxeq⟩ := hρ
      have hxeq' : σ₀⁻¹ * ρ = e x := hxeq.symm
      rw [hxeq', e.symm_apply_apply]
      exact hx
    have hmem : e.symm (σ₀⁻¹ * ρ) ∈ V :=
      hMV (e.symm (σ₀⁻¹ * ρ)) (Subgroup.mem_comap.mp hρ')
    have hprod : e.symm σ₀ * e.symm (σ₀⁻¹ * ρ) ∈ U := hmem
    have heq : e.symm ρ = e.symm σ₀ * e.symm (σ₀⁻¹ * ρ) := by
      rw [← map_mul]
      congr 1
      group
    show f (e.symm ρ) = f (e.symm σ₀)
    rw [heq]
    exact hUc _ hprod

/-! ## Roots of unity -/

/-- In a field of exponential characteristic `p`, the only `p^n`-th root of unity is `1`.  (In
characteristic zero `ringExpChar` is `1` and the statement is trivial.) -/
theorem expChar_pow_eq_one {p n : ℕ} [ExpChar Ω p] {ζ : Ωˣ} (h : ((ζ : Ω)) ^ p ^ n = 1) :
    ζ = 1 := by
  have h1 : ((ζ : Ω) - 1) ^ p ^ n = 0 := by rw [sub_pow_expChar_pow, h]; simp
  have h2 : (ζ : Ω) - 1 = 0 := eq_zero_of_pow_eq_zero h1
  exact Units.ext (sub_eq_zero.mp h2)

/-! ## Hilbert 90 for a general algebraic closure -/

/-- **Hilbert 90 for the absolute Galois group**, for an arbitrary base field.  Every locally
constant crossed homomorphism `Ω ≃ₐ[k] Ω → Ωˣ` is a coboundary.

The classical proof descends to a finite normal subextension `M/k` and applies Noether's finite
Hilbert 90 there.  In characteristic `p` the values of `f` need not lie in `M` (the fixed field of
`Gal(Ω/M)` is only the relative perfect closure of `M`), so instead a `p^n`-th power of every value
is brought into `M` (using `fixedField_expChar_pow`), the resulting crossed homomorphism on
`Gal(M/k)` is a coboundary `χ ↦ χ(β)/β` by finite Hilbert 90, and `f` is obtained by taking the
`p^n`-th root of `β` in the algebraically closed field `Ω`.  In characteristic `0` one has `p = 1`
and this reduces to the classical argument. -/
theorem hilbert90_isAlgClosure [IsAlgClosure k Ω] (f : (Ω ≃ₐ[k] Ω) → Ωˣ)
    (hf : ∀ σ τ : Ω ≃ₐ[k] Ω, f (σ * τ) = f σ * Work.SSGRoute.umap k Ω σ (f τ))
    (hc : Work.AbsoluteKummer.IsLocallyConstant f) :
    ∃ b : Ωˣ, ∀ σ : Ω ≃ₐ[k] Ω, f σ = Work.SSGRoute.umap k Ω σ b / b := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have : Normal k Ω := inferInstance
  have hf1 : f 1 = 1 := by
    have h := hf 1 1
    rw [one_mul, Work.SSGRoute.umap_one] at h
    exact mul_left_cancel (by rw [mul_one]; exact h.symm)
  obtain ⟨U, hUopen, h1U, hUc⟩ := hc 1
  have hfU : ∀ y ∈ U, f y = 1 := fun y hy => by rw [hUc y hy, hf1]
  have hUn : U ∈ 𝓝 (1 : Ω ≃ₐ[k] Ω) := hUopen.mem_nhds h1U
  obtain ⟨M, hMfin, hMnorm, hMsub⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal k Ω U).mp hUn
  have : FiniteDimensional k M := hMfin
  have : Normal k ↥M := hMnorm
  have hker : (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥M).ker = M.fixingSubgroup :=
    IntermediateField.restrictNormalHom_ker M
  have hNnormal : M.fixingSubgroup.Normal := by
    rw [← hker]; exact MonoidHom.normal_ker _
  have hfN : ∀ n ∈ M.fixingSubgroup, f n = 1 := fun n hn => hfU n (hMsub hn)
  have hNinv : ∀ (a n : Ω ≃ₐ[k] Ω), n ∈ M.fixingSubgroup → f (a * n) = f a := by
    intro a n hn
    rw [hf a n, hfN n hn, map_one, mul_one]
  have hfix : ∀ a : Ω ≃ₐ[k] Ω, ∀ n ∈ M.fixingSubgroup,
      n ((f a : Ωˣ) : Ω) = ((f a : Ωˣ) : Ω) := by
    intro a n hn
    have h1 : n * a = a * (a⁻¹ * n * a) := by group
    have h2 : a⁻¹ * n * a ∈ M.fixingSubgroup := hNnormal.conj_mem n hn a⁻¹
    have h3 : f (n * a) = f a := by rw [h1, hNinv a (a⁻¹ * n * a) h2]
    have h4 : f (n * a) = Work.SSGRoute.umap k Ω n (f a) := by
      rw [hf n a, hfN n hn, one_mul]
    have h5 : Work.SSGRoute.umap k Ω n (f a) = f a := by rw [← h4, h3]
    have := congrArg (fun u : Ωˣ => (u : Ω)) h5
    simpa [Work.SSGRoute.umap_coe] using this
  have hpow : ∀ a : Ω ≃ₐ[k] Ω, ∃ n : ℕ, ((f a : Ωˣ) : Ω) ^ (ringExpChar Ω ^ n) ∈ M :=
    fun a => fixedField_expChar_pow ((f a : Ωˣ) : Ω) (fun σ hσ => hfix a σ hσ)
  have hsurj : Function.Surjective (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥M) :=
    AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := ↥M) Ω
  let lift : (↥M ≃ₐ[k] ↥M) → (Ω ≃ₐ[k] Ω) := fun χ => Classical.choose (hsurj χ)
  have hlift : ∀ χ, AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥M (lift χ) = χ :=
    fun χ => Classical.choose_spec (hsurj χ)
  choose N hN using fun χ : (↥M ≃ₐ[k] ↥M) => hpow (lift χ)
  let Nap : ℕ := Finset.univ.sup N
  have hNap : ∀ χ : (↥M ≃ₐ[k] ↥M), ((f (lift χ) : Ωˣ) : Ω) ^ (ringExpChar Ω ^ Nap) ∈ M := by
    intro χ
    have hle : N χ ≤ Nap := Finset.le_sup (Finset.mem_univ χ)
    have hsplit : ringExpChar Ω ^ Nap
        = ringExpChar Ω ^ (Nap - N χ) * ringExpChar Ω ^ (N χ) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit, mul_comm, pow_mul]
    exact pow_mem (hN χ) _
  let g : (↥M ≃ₐ[k] ↥M) → (↥M)ˣ := fun χ =>
    Units.mk0 ⟨((f (lift χ) : Ωˣ) : Ω) ^ (ringExpChar Ω ^ Nap), hNap χ⟩ (by
      intro h0
      have h1 : ((f (lift χ) : Ωˣ) : Ω) ^ (ringExpChar Ω ^ Nap) = 0 := by
        simpa using congrArg Subtype.val h0
      exact pow_ne_zero _ (Units.ne_zero (f (lift χ))) h1)
  have hgval : ∀ χ : (↥M ≃ₐ[k] ↥M), ((g χ : (↥M)ˣ) : ↥M)
      = ⟨((f (lift χ) : Ωˣ) : Ω) ^ (ringExpChar Ω ^ Nap), hNap χ⟩ := fun χ => rfl
  have happ : ∀ (χ : ↥M ≃ₐ[k] ↥M) (x : ↥M), ((χ x : ↥M) : Ω) = (lift χ) (x : Ω) := by
    intro χ x
    conv_lhs => rw [← hlift χ]
    exact AlgEquiv.restrictNormalHom_apply (F := k) (K₁ := Ω) M (lift χ) x
  have hgcoc : ∀ χ ψ : (↥M ≃ₐ[k] ↥M),
      ((g (χ * ψ) : (↥M)ˣ) : ↥M) = ((g χ : (↥M)ˣ) : ↥M) * χ (((g ψ : (↥M)ˣ) : ↥M)) := by
    intro χ ψ
    have hn : (lift (χ * ψ))⁻¹ * (lift χ * lift ψ) ∈ M.fixingSubgroup := by
      rw [← hker, MonoidHom.mem_ker]
      simp only [map_mul, map_inv, hlift]
      group
    have hA : f (lift (χ * ψ)) = f (lift χ * lift ψ) := by
      have h := hNinv (lift (χ * ψ)) ((lift (χ * ψ))⁻¹ * (lift χ * lift ψ)) hn
      have heq : lift (χ * ψ) * ((lift (χ * ψ))⁻¹ * (lift χ * lift ψ)) = lift χ * lift ψ := by
        group
      rw [heq] at h
      exact h.symm
    have hK : ((f (lift (χ * ψ)) : Ωˣ) : Ω)
        = ((f (lift χ) : Ωˣ) : Ω) * (lift χ) (((f (lift ψ) : Ωˣ) : Ω)) := by
      have h := congrArg (fun u : Ωˣ => (u : Ω)) (hf (lift χ) (lift ψ))
      rw [hA]
      simpa [Work.SSGRoute.umap_coe] using h
    apply Subtype.ext
    show ((f (lift (χ * ψ)) : Ωˣ) : Ω) ^ (ringExpChar Ω ^ Nap)
      = (((g χ : (↥M)ˣ) : ↥M) : Ω) * ((χ (((g ψ : (↥M)ˣ) : ↥M)) : ↥M) : Ω)
    rw [hgval χ]
    rw [happ χ (((g ψ : (↥M)ˣ) : ↥M))]
    rw [hgval ψ]
    simp only [Subtype.coe_mk]
    rw [hK, mul_pow, map_pow]
  obtain ⟨β, hβ⟩ :=
    Work.AbsoluteKummer.exists_algEquiv_div_of_isCrossedHom (K := k) (L := ↥M) g hgcoc
  have hkpos : 0 < ringExpChar Ω ^ Nap := by
    apply pow_pos
    rw [show ringExpChar Ω = max (ringChar Ω) 1 from rfl]
    exact lt_of_lt_of_le Nat.one_pos (le_max_right _ 1)
  obtain ⟨b0, hb0⟩ := IsAlgClosed.exists_pow_nat_eq (((β : (↥M)ˣ) : ↥M) : Ω) hkpos
  have hb0ne : b0 ≠ 0 := by
    intro h0
    have h1 : (((β : (↥M)ˣ) : ↥M) : Ω) = 0 := by
      rw [← hb0, h0]
      exact zero_pow hkpos.ne'
    exact Units.ne_zero β (Subtype.coe_injective (by simpa using h1))
  let b : Ωˣ := Units.mk0 b0 hb0ne
  have hb : ((b : Ω) ^ (ringExpChar Ω ^ Nap)) = (((β : (↥M)ˣ) : ↥M) : Ω) := hb0
  refine ⟨b, fun σ => ?_⟩
  set χ : ↥M ≃ₐ[k] ↥M := AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥M σ with hχdef
  have hσeq : f σ = f (lift χ) := by
    have hmem : (lift χ)⁻¹ * σ ∈ M.fixingSubgroup := by
      rw [← hker, MonoidHom.mem_ker]
      simp only [map_mul, map_inv, hlift, hχdef]
      group
    have h := hNinv (lift χ) ((lift χ)⁻¹ * σ) hmem
    have heq : lift χ * ((lift χ)⁻¹ * σ) = σ := by group
    rw [heq] at h
    exact h
  have h1 : ((f σ : Ωˣ) : Ω) ^ (ringExpChar Ω ^ Nap)
      = σ (((β : (↥M)ˣ) : ↥M) : Ω) / (((β : (↥M)ˣ) : ↥M) : Ω) := by
    rw [hσeq]
    have hβχ := congrArg (fun z : ↥M => (z : Ω)) (hβ χ)
    rw [IntermediateField.coe_div] at hβχ
    rw [show (((g χ : (↥M)ˣ) : ↥M) : Ω)
        = ((f (lift χ) : Ωˣ) : Ω) ^ (ringExpChar Ω ^ Nap) from by rw [hgval χ]] at hβχ
    rw [show (((χ (((β : (↥M)ˣ) : ↥M))) : ↥M) : Ω)
        = σ (((β : (↥M)ˣ) : ↥M) : Ω) from by
      rw [hχdef]
      exact AlgEquiv.restrictNormalHom_apply (F := k) (K₁ := Ω) M σ ((β : (↥M)ˣ) : ↥M)] at hβχ
    exact hβχ
  have h3 : (σ ((b : Ω)) / ((b : Ω))) ^ (ringExpChar Ω ^ Nap)
      = σ (((β : (↥M)ˣ) : ↥M) : Ω) / (((β : (↥M)ˣ) : ↥M) : Ω) := by
    rw [div_pow, ← map_pow, hb]
  have hne : σ (((β : (↥M)ˣ) : ↥M) : Ω) / (((β : (↥M)ˣ) : ↥M) : Ω) ≠ 0 := by
    rw [← h1]
    exact pow_ne_zero _ (Units.ne_zero (f σ))
  have hq : (((f σ / (Work.SSGRoute.umap k Ω σ b / b) : Ωˣ)) : Ω) ^ (ringExpChar Ω ^ Nap)
      = 1 := by
    simp only [Units.val_div_eq_div_val, Work.SSGRoute.umap_coe]
    rw [div_pow, h1, h3, div_self hne]
  have hone := expChar_pow_eq_one hq
  have hfin : f σ = Work.SSGRoute.umap k Ω σ b / b := by
    conv_lhs => rw [← div_mul_cancel (f σ) (Work.SSGRoute.umap k Ω σ b / b)]
    rw [hone, one_mul]
  exact hfin

/-! ## Hilbert 90 for the fixing subgroup -/

/-- The subgroup action of `K.fixingSubgroup` on `Ωˣ` is the action of the corresponding
`K`-automorphism of `Ω`. -/
theorem fixingSubgroupEquiv_symm_smul_umap {K : IntermediateField k Ω} (σ : Ω ≃ₐ[K] Ω)
    (u : Additive Ωˣ) :
    (IntermediateField.fixingSubgroupEquiv K).symm σ • u
      = Additive.ofMul (Work.SSGRoute.umap ↥K Ω σ (Additive.toMul u)) := rfl

/-- **Hilbert 90 for `Gal(Ω/K)`**, `K` a finite intermediate field of an algebraic closure `Ω` of
`k`: every locally constant crossed homomorphism on `K.fixingSubgroup` with values in `Ωˣ` is a
coboundary. -/
theorem exists_div_fixingSubgroup [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K]
    (F : ↥(K.fixingSubgroup) → Additive Ωˣ)
    (hF : ∀ σ τ : ↥(K.fixingSubgroup), F (σ * τ) = σ • F τ + F σ)
    (hl : Work.AbsoluteKummer.IsLocallyConstant F) :
    ∃ b : Additive Ωˣ, ∀ σ : ↥(K.fixingSubgroup), F σ = σ • b - b := by
  have hAC : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  have := hAC
  set e := IntermediateField.fixingSubgroupEquiv K with he
  set f : (Ω ≃ₐ[K] Ω) → Ωˣ := fun σ => Additive.toMul (F (e.symm σ)) with hfdef
  have hfcross : ∀ σ τ : Ω ≃ₐ[K] Ω, f (σ * τ) = f σ * Work.SSGRoute.umap ↥K Ω σ (f τ) := by
    intro σ τ
    have h := hF (e.symm σ) (e.symm τ)
    have h2 : e.symm (σ * τ) = e.symm σ * e.symm τ := map_mul _ _ _
    show Additive.toMul (F (e.symm (σ * τ))) = Additive.toMul (F (e.symm σ)) *
      Work.SSGRoute.umap ↥K Ω σ (Additive.toMul (F (e.symm τ)))
    rw [h2, h, toMul_add,
      show ((e.symm σ) • F (e.symm τ))
        = Additive.ofMul (Work.SSGRoute.umap ↥K Ω σ (Additive.toMul (F (e.symm τ)))) from rfl]
    simp [mul_comm]
  have hfloc : Work.AbsoluteKummer.IsLocallyConstant f :=
    (Work.AbsoluteKummer.IsLocallyConstant.map Additive.toMul
      (locconst_fixingSubgroupEquiv_symm (K := K) hl))
  obtain ⟨b, hb⟩ := hilbert90_isAlgClosure (k := ↥K) f hfcross hfloc
  refine ⟨Additive.ofMul b, fun σ => ?_⟩
  have h1 : f (e σ) = Work.SSGRoute.umap ↥K Ω (e σ) b / b := hb (e σ)
  have h2 : f (e σ) = Additive.toMul (F σ) := by
    show Additive.toMul (F (e.symm (e σ))) = Additive.toMul (F σ)
    rw [e.symm_apply_apply]
  rw [h2] at h1
  have h3 : σ • (Additive.ofMul b)
      = Additive.ofMul (Work.SSGRoute.umap ↥K Ω (e σ) b) := by
    rw [show σ = e.symm (e σ) from (e.symm_apply_apply σ).symm]
    exact fixingSubgroupEquiv_symm_smul_umap (K := K) (e σ) (Additive.ofMul b)
  rw [h3]
  show F σ = Additive.ofMul (Work.SSGRoute.umap ↥K Ω (e σ) b / b)
  rw [← h1]
  exact (ofMul_toMul (F σ)).symm

end Work.SSGRoute
