import Mathlib
import Submission.Work.Drive.ProjectiveDefs

namespace Work.Drive

/-- `projLine U` is the carrier of the projective subspace `U.projectivization`: the set of points of
the projective space lying on the one-dimensional subspaces of `U`. -/
private theorem projLine_eq_projectivization {K V : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] (U : Submodule K V) :
    projLine U = (U.projectivization : Set (Projectivization K V)) := by
  ext p
  constructor
  · rintro ⟨v, hv, hvU, rfl⟩
    exact (Submodule.mk_mem_projectivization_iff U hv).2 hvU
  · intro hp
    -- every point of the projectivisation of `U` is represented by its own `rep`, a nonzero
    -- element of `U`.
    refine ⟨p.rep, p.rep_nonzero, ?_, (Projectivization.mk_rep p).symm⟩
    have hsub : p.submodule ≤ U := (Submodule.mem_projectivization_iff_submodule_le U p).1 hp
    refine hsub ?_
    rw [Projectivization.submodule_eq]
    exact Submodule.mem_span_singleton_self p.rep

/-- The projectivisation of a one-dimensional subspace is a single point. -/
private theorem ncard_projectivization_eq_one {K V : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] (H : Submodule K V) (h : Module.finrank K ↥H = 1) :
    ((H.projectivization : Set (Projectivization K V)).ncard = 1) := by
  -- `<v>` is a spanning nonzero vector of `H`; the single point is the class of `v`.
  obtain ⟨v, hv0, hvall⟩ := (finrank_eq_one_iff' (K := K) (V := ↥H)).1 h
  have hvv : (v : V) ≠ 0 := fun hc => hv0 (Subtype.ext (by simpa using hc))
  refine Set.ncard_eq_one.mpr ⟨Projectivization.mk K (v : V) hvv, ?_⟩
  ext x
  rw [Set.mem_singleton_iff]
  constructor
  · intro hx
    -- `x` lies on `H`, so a representative of `x` is a multiple of `v`.
    have hle : x.submodule ≤ H := (Submodule.mem_projectivization_iff_submodule_le H x).1 hx
    have hxrep : x.rep ∈ H := by
      refine hle ?_
      rw [Projectivization.submodule_eq]
      exact Submodule.mem_span_singleton_self x.rep
    obtain ⟨c, hc⟩ := hvall ⟨x.rep, hxrep⟩
    have hc' : c • (v : V) = x.rep := congrArg Subtype.val hc
    rw [← Projectivization.mk_rep x]
    exact (Projectivization.mk_eq_mk_iff' K x.rep (v : V) x.rep_nonzero hvv).2 ⟨c, hc'⟩
  · intro hx
    rw [hx]
    exact (Submodule.mk_mem_projectivization_iff H hvv).2 v.2

/-- **The linear parity fact of the `ℝ × ℝP³` model: three generic projective planes in `ℝP³` meet in
exactly one point.**

Modelling `ℝP³` as the projectivisation of `ℝ⁴` (`Submission.Work.Drive.ProjectiveDefs`), a projective
plane is `projLine U` for a `3`-dimensional subspace `U ⊆ ℝ⁴`.  If three such subspaces meet in a
one-dimensional subspace — the genericity condition making the three projective planes meet
transversally — then the three projective planes have exactly one common point of `ℝP³`: the point
represented by `U₁ ⊓ U₂ ⊓ U₃`.  Equivalently the count `((projLine U₁ ∩ projLine U₂) ∩ projLine U₃).ncard`
is `1`, which is odd.  This is the "three generic planes' images in `ℝP³` meet an odd number of times"
input named by the project lead for the mod-2 counting route to `Work.Drive.chainParity` (the three-fold
count `n_P + n_Q + n_R + n_λ + n_{-λ}` of Hugelmeyer's axioms 3 and 4).

Reason it holds: a point lying on all three projective planes is representable by a non-zero vector lying
in `U₁ ⊓ U₂` (pairwise case) and also in `U₃`, hence in the triple intersection, which is
one-dimensional by hypothesis; the projectivisation of a one-dimensional subspace is a single point. -/
theorem projective_planes_meet_oddly (U₁ U₂ U₃ : Submodule ℝ (EuclideanSpace ℝ (Fin 4)))
    (h1 : Module.finrank ℝ U₁ = 3) (h2 : Module.finrank ℝ U₂ = 3) (h3 : Module.finrank ℝ U₃ = 3)
    (htriple : Module.finrank ℝ ↥(U₁ ⊓ U₂ ⊓ U₃) = 1) :
    ((projLine U₁ ∩ projLine U₂) ∩ projLine U₃).ncard = 1 := by
  -- A point lies on all three projective planes exactly when it lies on the projectivisation of
  -- `U₁ ⊓ U₂ ⊓ U₃`: `U.projectivization` consists of the points whose associated line lies in `U`.
  have hset : (projLine U₁ ∩ projLine U₂) ∩ projLine U₃
      = ((U₁ ⊓ U₂ ⊓ U₃).projectivization :
          Set (Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))) := by
    ext x
    simp only [Set.mem_inter_iff, SetLike.mem_coe, projLine_eq_projectivization,
      Submodule.mem_projectivization_iff_submodule_le, le_inf_iff]
  rw [hset]
  exact ncard_projectivization_eq_one (U₁ ⊓ U₂ ⊓ U₃) htriple

end Work.Drive
