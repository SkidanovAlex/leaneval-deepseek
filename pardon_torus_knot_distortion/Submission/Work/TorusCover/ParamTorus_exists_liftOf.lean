import Mathlib
import Submission.Work.TorusCover.Basic
import Submission.Work.CoreTopology.Winding

/-!
# Lifts of closed curves on a parametrised torus

`Work.CoreTopology.LiftOf P γ` is a lift of a closed curve `γ` on the surface
`F = P.carrier` of a parametrised torus `P` to the parameter plane: a pair of continuous
functions `Θ Φ : ℝ → ℝ` with `P.psi (Θ t) (Φ t) = γ t` for all `t`.

The parametrisation `psiMap P.psi : ℝ × ℝ → F` is a covering map onto its image.  It is the
quotient map of the free, properly discontinuous action of the period lattice `2πℤ²` composed
with the homeomorphism `ℝ²/2πℤ² ≃ₜ F`; the latter is a continuous bijection from a compact
space (the image of the fundamental square `[0,2π]²`) onto the Hausdorff space `F`.  Hence
every continuous curve in `F` lifts, by the covering-space lifting theorem
`IsCoveringMap.existsUnique_continuousMap_lifts` applied to the simply connected, locally path
connected space `ℝ`.

The main technical inputs are

* `psiMap_eq_iff_param`: two parameter points have the same image under `P.psi` exactly when
  they differ by a lattice element (`P.inj_mod` combined with the description of the lattice);
* `exists_quot_repr` and `compactSpace_quot`: every coset of the lattice has a representative
  in the fundamental square, so that `ℝ²/2πℤ²` is compact;
* `quotMap` and `quotHomeo`: the induced map of the parametrisation on the quotient is a
  homeomorphism onto `F` (continuous bijection from a compact space onto a Hausdorff space);
* `isCoveringMap_psiMapToRange_param`: `psiMapToRange P.psi` is a covering map, obtained from
  Mathlib's `AddSubgroup.isAddQuotientCoveringMap_of_comm` (the quotient by a discrete
  subgroup of an abelian topological group is a covering map) by composing with `quotHomeo`.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.TorusCover

noncomputable section

section

variable (P : Work.CoreTopology.ParamTorus)

/-! ### Comparing parameter points -/

/-- Two parameter points of a parametrised torus have the same image exactly when they differ
by an element of the period lattice `2πℤ²`. -/
theorem psiMap_eq_iff_param {p q : ℝ × ℝ} :
    psiMap P.psi p = psiMap P.psi q ↔ p - q ∈ lattice := by
  rw [psiMap_apply, psiMap_apply, P.inj_mod p.1 p.2 q.1 q.2, mem_lattice_iff']
  constructor
  · rintro ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
    refine ⟨k, l, ?_⟩
    have h1 : p.1 - q.1 = (k : ℝ) * (2 * Real.pi) := by linarith
    have h2 : p.2 - q.2 = (l : ℝ) * (2 * Real.pi) := by linarith
    exact Prod.ext h1 h2
  · rintro ⟨k, l, h⟩
    refine ⟨⟨k, ?_⟩, ⟨l, ?_⟩⟩
    · have hh := congrArg Prod.fst h
      simp only [Prod.fst_sub] at hh
      linarith
    · have hh := congrArg Prod.snd h
      simp only [Prod.snd_sub] at hh
      linarith

/-- The lattice relation on the parameter plane implies a lattice displacement. -/
lemma sub_mem_lattice_of_leftRel {p q : ℝ × ℝ} (h : (QuotientAddGroup.leftRel lattice) p q) :
    p - q ∈ lattice := by
  have hmem : -p + q ∈ lattice := QuotientAddGroup.leftRel_apply.mp h
  have := lattice.neg_mem hmem
  simpa [neg_add, sub_eq_add_neg, add_comm] using this

/-- A lattice displacement gives the lattice relation on the parameter plane. -/
lemma leftRel_of_sub_mem_lattice {p q : ℝ × ℝ} (h : p - q ∈ lattice) :
    (QuotientAddGroup.leftRel lattice) p q := by
  rw [QuotientAddGroup.leftRel_apply]
  have := lattice.neg_mem h
  simpa [neg_add, sub_eq_add_neg, add_comm] using this

/-! ### The parametrisation on the quotient `ℝ²/2πℤ²` -/

/-- The parametrisation, viewed as a map onto the surface `P.carrier`. -/
def toCarrier : ℝ × ℝ → P.carrier := fun p => ⟨psiMap P.psi p, ⟨p, rfl⟩⟩

lemma toCarrier_continuous : Continuous (toCarrier P) :=
  Continuous.subtype_mk P.cont (fun p => ⟨p, rfl⟩)

/-- The parametrisation, factored through the quotient of the parameter plane by the period
lattice: a continuous bijection `ℝ²/2πℤ² → P.carrier`. -/
def quotMap : ((ℝ × ℝ) ⧸ lattice) → P.carrier :=
  Quotient.lift (toCarrier P)
    (fun _p _q h => Subtype.ext ((psiMap_eq_iff_param P).mpr (sub_mem_lattice_of_leftRel h)))

lemma quotMap_mk (p : ℝ × ℝ) : quotMap P (QuotientAddGroup.mk p) = toCarrier P p := rfl

lemma quotMap_continuous : Continuous (quotMap P) := by
  have hq : Topology.IsQuotientMap (QuotientAddGroup.mk (s := lattice)) :=
    QuotientAddGroup.isQuotientMap_mk lattice
  rw [hq.continuous_iff]
  exact (toCarrier_continuous P).congr (fun p => rfl)

lemma quotMap_surjective : Function.Surjective (quotMap P) := by
  intro x
  obtain ⟨p, hp⟩ : ∃ p : ℝ × ℝ, psiMap P.psi p = x.1 := x.2
  exact ⟨QuotientAddGroup.mk p, Subtype.ext hp⟩

lemma quotMap_injective : Function.Injective (quotMap P) := by
  intro a b hab
  obtain ⟨p, hp⟩ := Quotient.exists_rep a
  obtain ⟨q, hq⟩ := Quotient.exists_rep b
  rw [← hp, ← hq] at hab ⊢
  have h1 : psiMap P.psi p = psiMap P.psi q := by
    simpa [quotMap, toCarrier] using congrArg Subtype.val hab
  exact (Quotient.eq'').mpr (leftRel_of_sub_mem_lattice ((psiMap_eq_iff_param P).mp h1))

lemma quotMap_bijective : Function.Bijective (quotMap P) :=
  ⟨quotMap_injective P, quotMap_surjective P⟩

/-! ### Compactness of the quotient -/

/-- Every real number differs from an element of `[0, 2π]` by an integer multiple of `2π`. -/
lemma exists_int_sub_mem_Icc (x : ℝ) :
    ∃ k : ℤ, 0 ≤ x - (k : ℝ) * (2 * Real.pi) ∧ x - (k : ℝ) * (2 * Real.pi) ≤ 2 * Real.pi := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨⌊x / (2 * Real.pi)⌋, ?_, ?_⟩
  · have h : ((⌊x / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) ≤ x := by
      rw [← le_div_iff₀ hpi]
      exact Int.floor_le _
    linarith
  · have h : x < ((⌊x / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) + 2 * Real.pi := by
      have h' := Int.lt_floor_add_one (x / (2 * Real.pi))
      rw [div_lt_iff₀ hpi] at h'
      have : (((⌊x / (2 * Real.pi)⌋ + 1 : ℤ)) : ℝ) * (2 * Real.pi) =
          ((⌊x / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) + 2 * Real.pi := by
        push_cast
        ring
      linarith [h', this]
    linarith

/-- Every point of the quotient `ℝ²/2πℤ²` has a representative in the fundamental square
`[0, 2π] × [0, 2π]`. -/
lemma exists_quot_repr (p : ℝ × ℝ) :
    ∃ q ∈ (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi)),
      (QuotientAddGroup.mk q : (ℝ × ℝ) ⧸ lattice) = QuotientAddGroup.mk p := by
  obtain ⟨k, hk1, hk2⟩ := exists_int_sub_mem_Icc p.1
  obtain ⟨l, hl1, hl2⟩ := exists_int_sub_mem_Icc p.2
  refine ⟨(p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (l : ℝ) * (2 * Real.pi)),
    ⟨⟨hk1, hk2⟩, ⟨hl1, hl2⟩⟩, ?_⟩
  refine (Quotient.eq'').mpr (QuotientAddGroup.leftRel_apply.mpr ?_)
  have hq : -(p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (l : ℝ) * (2 * Real.pi)) + p
      = ((k : ℝ) * (2 * Real.pi), (l : ℝ) * (2 * Real.pi)) := by
    ext <;> simp
  rw [hq]
  exact (mem_lattice_iff' _).mpr ⟨k, l, rfl⟩

/-- The quotient of the parameter plane by the period lattice is compact (it is the image of
the fundamental square `[0, 2π]²`). -/
theorem compactSpace_quot : CompactSpace ((ℝ × ℝ) ⧸ lattice) := by
  refine isCompact_univ_iff.mp ?_
  have hD : IsCompact (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi)) :=
    isCompact_Icc.prod isCompact_Icc
  have himg : IsCompact (QuotientAddGroup.mk ''
      (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi)) :
      Set ((ℝ × ℝ) ⧸ lattice)) :=
    hD.image (QuotientAddGroup.continuous_mk (N := lattice))
  have huniv : (QuotientAddGroup.mk ''
      (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi)) :
      Set ((ℝ × ℝ) ⧸ lattice)) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro y
    obtain ⟨p, hp⟩ := QuotientAddGroup.mk_surjective y
    obtain ⟨q, hqD, hq⟩ := exists_quot_repr p
    exact ⟨q, hqD, by rw [hq, hp]⟩
  rw [huniv] at himg
  exact himg

/-! ### The torus as a quotient of the parameter plane -/

/-- **The parameter plane modulo its period lattice is the torus.**  The parametrisation
induces a homeomorphism `ℝ²/2πℤ² ≃ₜ P.carrier`: it is a continuous bijection from the compact
quotient onto the Hausdorff space `P.carrier`. -/
noncomputable def quotHomeo : ((ℝ × ℝ) ⧸ lattice) ≃ₜ P.carrier := by
  have : CompactSpace ((ℝ × ℝ) ⧸ lattice) := compactSpace_quot
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (quotMap P) (quotMap_bijective P))
    (by rw [Equiv.coe_ofBijective]; exact quotMap_continuous P)

/-- **The parametrisation of a `ParamTorus` is a covering map onto its image.**  The map is the
quotient covering `ℝ² → ℝ²/2πℤ²` followed by the homeomorphism `quotHomeo`. -/
theorem isCoveringMap_psiMapToRange_param : IsCoveringMap (psiMapToRange P.psi) := by
  have hcov : IsAddQuotientCoveringMap
      (QuotientAddGroup.mk : ℝ × ℝ → (ℝ × ℝ) ⧸ lattice) lattice :=
    AddSubgroup.isAddQuotientCoveringMap_of_comm lattice isDiscrete_lattice
  have h2 : IsAddQuotientCoveringMap (⇑(quotHomeo P) ∘ QuotientAddGroup.mk) lattice :=
    IsAddQuotientCoveringMap.homeomorph_comp hcov (quotHomeo P)
  have h3 : IsCoveringMap (⇑(quotHomeo P) ∘ QuotientAddGroup.mk) := h2.isCoveringMap
  have hfun : (⇑(quotHomeo P) ∘ QuotientAddGroup.mk) = psiMapToRange P.psi := by
    funext p
    exact Subtype.ext rfl
  rwa [hfun] at h3

end

/-! ### Existence of lifts -/

/-- **Every closed curve on a parametrised torus lifts to the parameter plane.**  A closed
curve on the surface `F = P.carrier` of a parametrised torus admits a lift `(Θ, Φ) : ℝ → ℝ²`,
i.e. a pair of continuous functions with `P.psi (Θ t) (Φ t) = γ t` for all `t`.

This is the covering-space path-lifting theorem applied to the covering map
`psiMapToRange P.psi` and the simply connected, locally path connected space `ℝ`. -/
theorem ParamTorus_exists_liftOf (P : Work.CoreTopology.ParamTorus)
    (γ : Work.CoreTopology.ClosedCurve P) :
    Nonempty (Work.CoreTopology.LiftOf P γ) := by
  have hcov : IsCoveringMap (psiMapToRange P.psi) := isCoveringMap_psiMapToRange_param P
  -- a point of the parameter plane lying over `γ 0`
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : ℝ × ℝ, psiMap P.psi p₀ = γ.γ 0 := γ.mem 0
  -- the curve, as a continuous map into the range of `psi`
  have hcont : Continuous fun t : ℝ => (⟨γ.γ t, γ.mem t⟩ : Set.range (psiMap P.psi)) :=
    Continuous.subtype_mk γ.cont (fun t => γ.mem t)
  obtain ⟨F, ⟨_hF0, hFlift⟩, -⟩ :=
    hcov.existsUnique_continuousMap_lifts
      (⟨fun t => ⟨γ.γ t, γ.mem t⟩, hcont⟩ : C(ℝ, Set.range (psiMap P.psi))) 0 p₀
      (Subtype.ext hp₀)
  refine ⟨{ Θ := fun t => (F t).1, Φ := fun t => (F t).2,
            contΘ := continuous_fst.comp F.continuous,
            contΦ := continuous_snd.comp F.continuous,
            lifts := fun t => ?_ }⟩
  have h := congrArg Subtype.val (congr_fun hFlift t)
  simpa [psiMap] using h

end

end Work.TorusCover
