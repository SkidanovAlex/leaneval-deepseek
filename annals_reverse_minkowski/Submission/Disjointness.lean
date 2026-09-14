import Mathlib
import Submission.Intrinsic
import Submission.FundBody
import Submission.Cvp

open Module Real MeasureTheory
open scoped Real BigOperators InnerProductSpace RealInnerProductSpace Pointwise
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false

/-!
# Fundamental-body disjointness of the ambient product cell ([C]-final, disjointness)

The boundary case of `gamma_stable_of_two_le` needs, for the host lattice `ℒ` and a
primitive sublattice `ℒ₁`, the set `K := V(ℒ₁ ⊔ Q)` (`Q := quotLattice ℒ (realSpan ℒ₁)`)
to satisfy the *fundamental-body translate disjointness* over `ℒ`-translates:

    ∀ y : ℒ, y ≠ 0 → Disjoint (interior K) ((y : E) +ᵥ K)     (`voronoi_interior_disjoint`)

This is the `hKdisj` hypothesis of `monotone_Voronoi_wins` (Cvp).  The proof follows the
paper's Claim 2.4 (fundamental_product): split the ambient space as `S ⊕ Sᗮ` with
`S := realSpan ℒ₁`; decompose `x ∈ interior K ∩ (y + K)` into its `S`- and `Sᗮ`-parts;
the `Sᗮ`-part `πx` lies in the interior of the in-complement cell `C₂` of `Q` while
`πx − πy ∈ C₂`, contradicting the intrinsic (in-span) translate disjointness of `Q`'s cell
(`compl_cell_disjoint_of_mem`, derived from `Intrinsic.inSpan_voronoi_disjoint_of_ambient_mem`
through the `realSpanIso`-transport); hence `πy = 0`, i.e. `y ∈ realSpan ℒ₁`, and by
primitivity `y ∈ ℒ₁ ⊆ ℒ₁ ⊔ Q` — a nonzero lattice point of `ℒ₁ ⊔ Q`, contradicting the
ambient translate disjointness of the Voronoi cell of `ℒ₁ ⊔ Q` itself
(`Intrinsic.voronoi_interior_disjoint_ambient`).
-/

namespace Submission.Disjointness

noncomputable section

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "VC" => Submission.Voronoi.voronoi
local notation "W" => Submission.QuotientLattice.realSpan

/-- The Sᗮ-component of a difference is the difference of the components. -/
lemma phiOf_symmP_component₂_sub (S : Submodule ℝ E) (a b : E) :
    (Submission.FundBody.phiOf_symmP S (a - b)).2 = (Submission.FundBody.phiOf_symmP S a).2 - (Submission.FundBody.phiOf_symmP S b).2 := by
  apply Subtype.ext
  have h1 (z : E) : (((Submission.FundBody.phiOf_symmP S z).2 : ↥(Sᗮ)) : E) = z - S.starProjection z := by
    dsimp [Submission.FundBody.phiOf_symmP]
    simpa [Submission.FundBody.phiOf_symmP_w, Submodule.coe_orthogonalProjectionOnto_apply]
  change (((Submission.FundBody.phiOf_symmP S (a - b)).2 : ↥(Sᗮ)) : E) =
    ((((Submission.FundBody.phiOf_symmP S a).2 : ↥(Sᗮ)) - (Submission.FundBody.phiOf_symmP S b).2) : E)
  rw [h1 (a - b), h1 a, h1 b]
  simp [Submodule.coe_sub]
  abel

/-- The Sᗮ-component of a point of the sum-set lies in the second summand. -/
lemma sum_component_mem (S : Submodule ℝ E) (C₁ : Set (↥S)) (C₂ : Set (↥(Sᗮ)))
    {x : E} (hx : x ∈ {x : E | ∃ u ∈ C₁, ∃ v ∈ C₂, (u : E) + (v : E) = x}) :
    (Submission.FundBody.phiOf_symmP S x).2 ∈ C₂ := by
  rcases hx with ⟨u, hu, v, hv, hxuv⟩
  have hφ : Submission.FundBody.phiOf S (u, v) = x := by
    dsimp [Submission.FundBody.phiOf]
    exact hxuv
  have hx2 : (Submission.FundBody.phiOf_symmP S x).2 = v := by
    calc
      (Submission.FundBody.phiOf_symmP S x).2 = (Submission.FundBody.phiOf_symmP S (Submission.FundBody.phiOf S (u, v))).2 := by rw [hφ]
      _ = ((u, v) : ↥S × ↥(Sᗮ)).2 := by rw [Submission.FundBody.phiOf_symmP_symm_apply S (u, v)]
      _ = v := rfl
  rw [hx2]
  exact hv

/-- Set translate-disjointness transfers along a (linear) isometry. -/
lemma disjoint_image_transport {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] (f : A ≃ₗᵢ[ℝ] B) {C : Set A} {D : Set B}
    (hCD : f '' C = D) {a : A}
    (hD : Disjoint (interior D) (((f a : B) +ᵥ D))) :
    Disjoint (interior C) (((a : A) +ᵥ C)) := by
  rw [Set.disjoint_left]
  intro x hxI hxT
  have fxI : (f x) ∈ interior D := by
    have himg : (f '' interior C) = interior (f '' C) :=
      (Homeomorph.image_interior (f.toHomeomorph) C)
    have hmem : f x ∈ f '' interior C := ⟨x, hxI, rfl⟩
    rw [himg, hCD] at hmem
    exact hmem
  have fxT : (f x) ∈ ((f a : B) +ᵥ D) := by
    rw [Set.mem_vadd_set]
    rcases (Set.mem_vadd_set.mp hxT) with ⟨c, hc, hxac⟩
    refine ⟨f c, ?_, ?_⟩
    · rw [← hCD]
      exact ⟨c, hc, rfl⟩
    · change (f a : B) + (f c : B) = f x
      rw [← f.map_add]
      exact congrArg (fun z : A => (f : A → B) z) hxac
  exact (Set.disjoint_left.mp hD) fxI fxT

/-- Translate-disjointness of the ambient Voronoi cell restricted to an orthogonal
complement: for a lattice `ℒ₂` whose real span is `W₁ᗮ`, the in-complement cell has
interior disjoint from translates by nonzero lattice points. -/
theorem compl_cell_disjoint_of_mem (ℒ₂ : Submodule ℤ E) [DiscreteTopology ℒ₂]
    {W₁ : Submodule ℝ E} (hR : W ℒ₂ = W₁ᗮ) :
    ∀ q : ↥(W₁ᗮ), q ≠ 0 → (q : E) ∈ ℒ₂ → Disjoint
      (interior {v : ↥(W₁ᗮ) | (v : E) ∈ VC (ℒ := ℒ₂)})
      (((q : ↥(W₁ᗮ)) +ᵥ {v : ↥(W₁ᗮ) | (v : E) ∈ VC (ℒ := ℒ₂)})) := by
  classical
  intro q hq0 hqmem
  let f : ↥(W₁ᗮ) ≃ₗᵢ[ℝ] ↥(W ℒ₂) := Submission.FundBody.subCast (W₁ᗮ) (W ℒ₂) hR.symm
  let C : Set (↥(W₁ᗮ)) := {v : ↥(W₁ᗮ) | (v : E) ∈ VC (ℒ := ℒ₂)}
  let D : Set (↥(W ℒ₂)) := {z : ↥(W ℒ₂) | (z : E) ∈ VC (ℒ := ℒ₂)}
  have hCD : f '' C = D := by
    dsimp [C, D]
    ext z
    constructor
    · rintro ⟨v, hv, hz⟩
      have hzE : (z : E) = (v : E) := by
        rw [← hz]
        exact Submission.FundBody.subCast_apply (W₁ᗮ) (W ℒ₂) hR.symm v
      change (z : E) ∈ VC (ℒ := ℒ₂)
      rw [hzE]
      exact hv
    · intro hz
      let v : ↥(W₁ᗮ) := (f.symm) z
      refine ⟨v, ?_, ?_⟩
      · have hvE : (v : E) = (z : E) := by
          dsimp [v, f]
          calc
            (((Submission.FundBody.subCast (W₁ᗮ) (W ℒ₂) hR.symm).symm z : ↥(W₁ᗮ)) : E)
                = (((Submission.FundBody.subCast (W₁ᗮ) (W ℒ₂) hR.symm)
                    ((Submission.FundBody.subCast (W₁ᗮ) (W ℒ₂) hR.symm).symm z) : ↥(W ℒ₂)) : E) := by
                    rw [← Submission.FundBody.subCast_apply (W₁ᗮ) (W ℒ₂) hR.symm
                      ((Submission.FundBody.subCast (W₁ᗮ) (W ℒ₂) hR.symm).symm z)]
            _ = (z : E) := by
                    exact congrArg (fun w : ↥(W ℒ₂) => (w : E))
                      ((Submission.FundBody.subCast (W₁ᗮ) (W ℒ₂) hR.symm).apply_symm_apply z)
        change (v : E) ∈ VC (ℒ := ℒ₂)
        rw [hvE]
        exact hz
      · rfl
  have hq' : (f q : ↥(W ℒ₂)) ≠ 0 := by
    intro hz
    apply hq0
    have hval : (f q : E) = 0 := congrArg (fun z : ↥(W ℒ₂) => (z : E)) hz
    have hqval : (q : E) = 0 := by
      rw [← Submission.FundBody.subCast_apply (W₁ᗮ) (W ℒ₂) hR.symm q]
      exact hval
    exact Subtype.ext hqval
  have hq'mem : ((f q : ↥(W ℒ₂)) : E) ∈ ℒ₂ := by
    have hcast : ((f q : ↥(W ℒ₂)) : E) = (q : E) := by
      dsimp [f]
      exact Submission.FundBody.subCast_apply (W₁ᗮ) (W ℒ₂) hR.symm q
    rwa [hcast]
  have hmain := Submission.Intrinsic.inSpan_voronoi_disjoint_of_ambient_mem (ℒ := ℒ₂) (f q) hq' hq'mem
  -- hmain: Disjoint (interior {z : ↥(W ℒ₂) | (z : E) ∈ VC ℒ₂}) (((f q) +ᵥ {z | ...}))
  have hD' : Disjoint (interior D) ((((f q : ↥(W ℒ₂)) +ᵥ D))) := by
    dsimp [D]
    exact hmain
  exact disjoint_image_transport f (C := C) (D := D) hCD (a := q) (by
    dsimp [f]
    exact hD')


/-- Fundamental-body disjointness of `V(ℒ₁ ⊔ Q)` over `ℒ`-translates. -/
theorem voronoi_interior_disjoint (ℒ₁ ℒ : Submodule ℤ E)
    [DiscreteTopology ℒ₁] [DiscreteTopology ℒ]
    (hΛd : DiscreteTopology ((ℒ₁ ⊔ (Submission.QuotientLattice.quotLattice ℒ (W ℒ₁))) : Submodule ℤ E))
    (hQd : DiscreteTopology ((Submission.QuotientLattice.quotLattice ℒ (W ℒ₁)) : Submodule ℤ E))
    (hle : ℒ₁ ≤ ℒ)
    (hp : ∀ x, x ∈ ℒ₁ ↔ x ∈ ℒ ∧ x ∈ W ℒ₁)
    (hop : Submission.QuotientLattice.OrthogonalPair ℒ₁ (Submission.QuotientLattice.quotLattice ℒ (W ℒ₁)))
    (hR : W (Submission.QuotientLattice.quotLattice ℒ (W ℒ₁)) = (W ℒ₁)ᗮ) :
    ∀ y : ℒ, y ≠ 0 → Disjoint
      (interior (VC (ℒ₁ ⊔ Submission.QuotientLattice.quotLattice ℒ (W ℒ₁))))
      (((y : E) +ᵥ (VC (ℒ₁ ⊔ Submission.QuotientLattice.quotLattice ℒ (W ℒ₁))))) := by
  classical
  let S : Submodule ℝ E := W ℒ₁
  let Q : Submodule ℤ E := Submission.QuotientLattice.quotLattice ℒ (W ℒ₁)
  intro y hy0
  rw [Set.disjoint_left]
  intro x hxI hxT
  let C₁ : Set (↥S) := {u : ↥S | (u : E) ∈ VC (ℒ := ℒ₁)}
  let C₂ : Set (↥(Sᗮ)) := {v : ↥(Sᗮ) | (v : E) ∈ VC (ℒ := Q)}
  have hKsum : VC (ℒ := (ℒ₁ ⊔ Q)) =
      {x : E | ∃ u ∈ C₁, ∃ v ∈ C₂, (u : E) + (v : E) = x} := by
    dsimp [C₁, C₂, S, Q]
    exact Submission.FundBody.voronoi_sup_eq_cell_sum ℒ₁ Q hop hR
  have hxI' : x ∈ interior {x : E | ∃ u ∈ C₁, ∃ v ∈ C₂, (u : E) + (v : E) = x} := by
    rw [← hKsum]
    exact hxI
  -- πx ∈ interior C₂ (the T-component of an interior point)
  have hπxI : (Submission.FundBody.phiOf_symmP S x).2 ∈ interior C₂ := by
    exact Submission.FundBody.interior_sum_component S C₁ C₂ hxI'
  -- x − y ∈ K
  have hxTr' : x - (y : E) ∈ VC (ℒ := (ℒ₁ ⊔ Q)) := by
    rcases (Set.mem_vadd_set.mp hxT) with ⟨k, hk, hxyk⟩
    have hkxy : k = x - (y : E) := by
      change (y : E) + k = x at hxyk
      simpa using (congrArg (fun z : E => z - (y : E)) hxyk)
    rwa [hkxy] at hk
  have hxTsum : x - (y : E) ∈ {x : E | ∃ u ∈ C₁, ∃ v ∈ C₂, (u : E) + (v : E) = x} := by
    rw [← hKsum]
    exact hxTr'
  -- π(x−y) = πx − πy ∈ C₂
  let πx : ↥(Sᗮ) := (Submission.FundBody.phiOf_symmP S x).2
  let πy : ↥(Sᗮ) := (Submission.FundBody.phiOf_symmP S (y : E)).2
  have hπxsub : πx - πy ∈ C₂ := by
    have hc := sum_component_mem S C₁ C₂ (x := x - (y : E)) hxTsum
    dsimp [πx, πy] at hc ⊢
    rwa [phiOf_symmP_component₂_sub S x (y : E)] at hc
  have hπxTr : πx ∈ (((πy : ↥(Sᗮ)) +ᵥ C₂)) := by
    rw [Set.mem_vadd_set]
    refine ⟨πx - πy, hπxsub, ?_⟩
    change πy + (πx - πy) = πx
    abel
  have hπxI' : πx ∈ interior C₂ := by
    simpa [πx] using hπxI
  -- πy ∈ Q
  have hπymem : ((πy : ↥(Sᗮ)) : E) ∈ Q := by
    dsimp [πy, S, Q]
    exact Submission.FundBody.phiOf_symmP_component_mem_quotLattice ℒ₁ ℒ y
  have hπy0 : πy = 0 := by
    by_contra hπyne
    have hdisj := compl_cell_disjoint_of_mem (ℒ₂ := Q) (W₁ := S) hR (q := πy) hπyne hπymem
    -- C₂ is the in-complement cell set of Q
    exact (Set.disjoint_left.mp hdisj) (by simpa [C₂] using hπxI') (by simpa [C₂, πy] using hπxTr)
  -- (y : E) ∈ S
  have hyS : (y : E) ∈ (S : Set E) := by
    have hdec : (y : E) = ((Submission.FundBody.phiOf_symmP S (y : E)).1 : E) +
        ((Submission.FundBody.phiOf_symmP S (y : E)).2 : E) := by
      have h := Submission.FundBody.phiOf_symmP_apply_symm S (y : E)
      -- h : (phiOf S (phiOf_symmP S (y:E)) : E) = (y : E)
      change ((Submission.FundBody.phiOf_symmP S (y : E)).1 : E) +
        ((Submission.FundBody.phiOf_symmP S (y : E)).2 : E) = (y : E) at h
      exact h.symm
    have hπyval : ((Submission.FundBody.phiOf_symmP S (y : E)).2 : E) = 0 := by
      have hv := congrArg (fun z : ↥(Sᗮ) => (z : E)) hπy0
      simpa using hv
    rw [hdec, hπyval, add_zero]
    exact (Submission.FundBody.phiOf_symmP S (y : E)).1.2
  -- primitive ⇒ (y : E) ∈ ℒ₁
  have hyL1 : (y : E) ∈ ℒ₁ := by
    exact (hp (y : E)).mpr ⟨y.2, by simpa [S] using hyS⟩
  -- y is a nonzero lattice point of Λ := ℒ₁ ⊔ Q
  let Λ : Submodule ℤ E := ℒ₁ ⊔ Q
  have hyΛ : (y : E) ∈ Λ := by
    dsimp [Λ]
    exact Submodule.mem_sup.mpr ⟨(y : E), hyL1, 0, Submodule.zero_mem Q, by simp⟩
  let z : Λ := ⟨(y : E), hyΛ⟩
  have hz0 : z ≠ 0 := by
    intro hzz
    apply hy0
    apply Subtype.ext
    exact congrArg (fun w : Λ => (w : E)) hzz
  haveI : DiscreteTopology Λ := by
    dsimp [Λ, Q]
    exact hΛd
  have h1 := Submission.Intrinsic.voronoi_interior_disjoint_ambient (n := m) (ℒ := Λ) z hz0
  have hxI'' : x ∈ interior (VC (ℒ := Λ)) := by
    dsimp [Λ]
    exact hxI
  have hxT'' : x ∈ (((z : E) +ᵥ (VC (ℒ := Λ)))) := by
    dsimp [z]
    exact hxT
  exact (Set.disjoint_left.mp h1) hxI'' hxT''

end

end Submission.Disjointness

