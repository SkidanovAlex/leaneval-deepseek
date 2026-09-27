import Mathlib
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLNonExc.DinjFacts
import Submission.Work.EKLComp.locallyFree_compacta
import Submission.Work.EKLComp.uniform_inj_of_isCompact
import Submission.Work.EKLComp.isClosed_Ucl
import Submission.Work.EKLComp.exists_isCompact_image
import Submission.Work.EKLComp.isClosed_exists_smul_eq_of_isCompact
import Submission.Work.EKLProd.sl3EntryBox_compact

/-!
# `Work.EKLRelCross.exists_inj_nhds`

Pisa (Einsiedler–Lindenstrauss) §6.8: if the `U`-orbit of `x₀ ∈ X₃ = SL₃(ℝ)/SL₃(ℤ)` is free and
`U ≤ SL₃(ℝ)` is closed, then the orbit map `u ↦ u • x` is injective on the *closed* displacement
ball `Ucl U R = {u ∈ U | |uᵢⱼ − δᵢⱼ| ≤ R}` for **all** `x` in a compact neighbourhood `E` of `x₀`,
uniformly in the radius `R`.

The proof combines two facts:

* *local freeness* (`Work.EKLComp.uniform_inj_of_isCompact`, imported): on the compact set `K`
  there is `η > 0` such that two elements of `V η` that move a point of `K` to the same place are
  equal — in particular a displacement in `V η` fixing `x ∈ K` is the identity;
* *compactness*: the difference set `A = (Ucl U R)⁻¹ * Ucl U R` is compact (it is a product of
  compact sets, `Ucl U R` being a closed subset of a compact entrywise box), so the set of pairs
  `(x, g) ∈ K × A` with `g ∉ V η` and `g • x = x` is closed in the compact space `↥A × X₃`; its
  projection to `X₃` — the "bad set" of points of `K` fixed by a displacement outside `V η` — is
  therefore closed, and it does not contain `x₀` because `x₀`'s `U`-orbit is free and `1 ∈ V η`.
  A compact neighbourhood of `x₀` inside the complement of the bad set is the required `E`.
-/

namespace Work.EKLRelCross

open scoped Pointwise

open Work.EKLContract

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- `Ucl U R` is compact when the subgroup `U` is closed: it is a closed subset of the compact
entrywise box of radius `R` (translated around the identity). -/
theorem isCompact_Ucl_of_isClosed {U : Subgroup SL3} (hU : IsClosed (U : Set SL3)) (R : ℝ) :
    IsCompact (Ucl U R) := by
  refine (Work.EKLProd.sl3EntryBox_compact
    (fun i j => (1 : Matrix (Fin 3) (Fin 3) ℝ) i j - R)
    (fun i j => (1 : Matrix (Fin 3) (Fin 3) ℝ) i j + R)).of_isClosed_subset
      (Work.EKLComp.isClosed_Ucl U hU R) ?_
  intro g hg i j
  have h := hg.2 i j
  rw [abs_le] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The difference set `(Ucl U R)⁻¹ * Ucl U R` is contained in `U`. -/
theorem inv_Ucl_mul_Ucl_subset (U : Subgroup SL3) (R : ℝ) :
    (Ucl U R)⁻¹ * Ucl U R ⊆ (U : Set SL3) := by
  intro g hg
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hg
  have haU : a ∈ U := by
    simpa using U.inv_mem (Set.mem_inv.mp ha).1
  exact U.mul_mem haU hb.1

theorem exists_inj_nhds {U : Subgroup Work.EKLContract.SL3} (hU : IsClosed (U : Set Work.EKLContract.SL3)) (x₀ : Work.EKLContract.X3)
    (hfree : ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x₀ = u₂ • x₀ → u₁ = u₂) {R : ℝ} :
    ∃ E : Set Work.EKLContract.X3, IsCompact E ∧ x₀ ∈ interior E ∧
      ∀ x ∈ E, ∀ u ∈ Work.EKLRelCross.Ucl U R, ∀ u' ∈ Work.EKLRelCross.Ucl U R, u • x = u' • x → u = u' := by
  classical
  haveI : IsClosed (Γ3 : Set SL3) := Work.EKLContract.Lemmas.isClosed_Γ3
  haveI : LocallyCompactSpace X3 := inferInstance
  -- Step 1: a compact neighbourhood `K` of `x₀` and the local-freeness radius on it.
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds x₀
  have hx₀K : x₀ ∈ interior K := mem_interior_iff_mem_nhds.mpr hKn
  obtain ⟨η, hη, hloc⟩ := Work.EKLComp.uniform_inj_of_isCompact K hKc
  have hVopen : IsOpen (V η) := (Work.EKLContract.Lemmas.V_open_one η hη).1
  have h1V : (1 : SL3) ∈ V η := (Work.EKLContract.Lemmas.V_open_one η hη).2
  -- Step 2: the compact difference set.
  have hAc : IsCompact ((Ucl U R)⁻¹ * Ucl U R) :=
    (isCompact_Ucl_of_isClosed hU R).inv.mul (isCompact_Ucl_of_isClosed hU R)
  have hA'c : IsCompact (((Ucl U R)⁻¹ * Ucl U R) ∩ (V η)ᶜ) :=
    hAc.of_isClosed_subset (hAc.isClosed.inter hVopen.isClosed_compl) Set.inter_subset_left
  -- Step 3: the bad set — points of `K` fixed by a displacement of `A` outside `V η`.
  set Bad : Set X3 :=
    {x : X3 | x ∈ K ∧ ∃ g ∈ (Ucl U R)⁻¹ * Ucl U R, g ∉ V η ∧ g • x = x} with hBaddef
  have hBadClosed : IsClosed Bad := by
    rw [hBaddef]
    have hRc : IsClosed
        {p : X3 × X3 | ∃ g ∈ ((Ucl U R)⁻¹ * Ucl U R) ∩ (V η)ᶜ, g • p.1 = p.2} :=
      Work.EKLComp.isClosed_exists_smul_eq_of_isCompact _ hA'c
    have heq : {x : X3 | x ∈ K ∧ ∃ g ∈ (Ucl U R)⁻¹ * Ucl U R, g ∉ V η ∧ g • x = x}
        = K ∩ (fun x : X3 => (x, x)) ⁻¹'
            {p : X3 × X3 | ∃ g ∈ ((Ucl U R)⁻¹ * Ucl U R) ∩ (V η)ᶜ, g • p.1 = p.2} := by
      ext x
      constructor
      · rintro ⟨hxK, g, hgA, hgV, hgx⟩
        exact ⟨hxK, g, ⟨hgA, hgV⟩, hgx⟩
      · rintro ⟨hxK, g, ⟨hgA, hgV⟩, hgx⟩
        exact ⟨hxK, g, hgA, hgV, hgx⟩
    rw [heq]
    exact hKc.isClosed.inter (hRc.preimage (continuous_id.prodMk continuous_id))
  -- Step 4: `x₀` is not bad, by freeness of its `U`-orbit.
  have hx₀Bad : x₀ ∉ Bad := by
    rw [hBaddef]
    rintro ⟨-, g, hgA, hgV, hgx⟩
    have hgU : g ∈ U := inv_Ucl_mul_Ucl_subset U R hgA
    have hg1 : g = 1 := hfree g hgU 1 U.one_mem (by rw [hgx, one_smul])
    exact hgV (hg1 ▸ h1V)
  -- Step 5: a compact neighbourhood of `x₀` inside the complement of the bad set.
  have hopen : IsOpen (Badᶜ ∩ interior K) := hBadClosed.isOpen_compl.inter isOpen_interior
  have hmem : x₀ ∈ Badᶜ ∩ interior K := ⟨hx₀Bad, hx₀K⟩
  obtain ⟨E, hEc, hx₀E, hEsub⟩ := exists_compact_subset hopen hmem
  refine ⟨E, hEc, hx₀E, ?_⟩
  intro x hxE u hu u' hu' heq
  obtain ⟨hxBad, hxIntK⟩ := hEsub hxE
  have hxK : x ∈ K := interior_subset hxIntK
  -- the displacement taking `x` to itself
  set g : SL3 := u⁻¹ * u' with hgdef
  have huinv : u⁻¹ ∈ (Ucl U R)⁻¹ := by
    rw [Set.mem_inv]
    simpa using hu
  have hgA : g ∈ (Ucl U R)⁻¹ * Ucl U R := by
    rw [hgdef]
    exact Set.mul_mem_mul huinv hu'
  have hgx : g • x = x := by
    rw [hgdef, mul_smul, ← heq, ← mul_smul, inv_mul_cancel, one_smul]
  by_cases hgV : g ∈ V η
  · -- a displacement in `V η` fixing a point of the compact set `K` is trivial
    have hg1 : g = 1 := hloc x hxK g 1 hgV h1V (by rw [hgx, one_smul])
    rw [hgdef] at hg1
    have h2 : u * (u⁻¹ * u') = u * 1 := congrArg (fun z : SL3 => u * z) hg1
    rw [mul_one] at h2
    rw [← mul_assoc, mul_inv_cancel, one_mul] at h2
    exact h2.symm
  · -- a displacement outside `V η` fixing `x ∈ K` would put `x` in the bad set
    have hxBad' : x ∈ Bad := by
      rw [hBaddef]
      exact ⟨hxK, g, hgA, hgV, hgx⟩
    exact absurd hxBad' hxBad

end Work.EKLRelCross
