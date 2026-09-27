import Mathlib
import Submission.Work.EQ.UnivCover.Defs
import Submission.Work.EQ.UnivCover.Sheet
import Submission.Work.EQ.UnivCover.Topology
import Submission.Work.EQ.UnivCover.Cover
import Submission.Work.EQ.UnivCover.UC_continuous_segPt

/-!
# The universal cover has no non-trivial homomorphism of its fundamental group to `ℝ`

The total space `UC x₀` of the universal cover of `X` (based at `x₀`) is simply connected: its
fundamental group is trivial.  Consequently there is at most one additive homomorphism from it to
`ℝ` (the zero one).

The proof goes through the monodromy action of the covering `UC.proj : UC x₀ → X` on the fibre
over `x₀`.  The fibre is canonically `Path.Homotopic.Quotient x₀ x₀` via `e ↦ e.cls`, and the
monodromy of a loop `ζ` moves `e` to `⟨x₀, e.cls.trans ζ⟩`; in particular the monodromy action is
free.  Since a loop in `UC x₀` at the base point projects to a loop whose monodromy fixes the base
point (the lift of its own projection), it must be null-homotopic.
-/

set_option autoImplicit false
open _root_.Topology
open scoped Topology

namespace Work.EQ.UnivCover

section Basics

variable {X : Type*} [TopologicalSpace X] {x₀ : X}

/-- `UC.segPt γ 0` is the base point of the universal cover. -/
theorem UC.segPt_zero {x : X} (γ : Path x₀ x) : UC.segPt γ 0 = UC.base x₀ := by
  have hq : Path.Homotopic.Quotient.mk (segTo γ 0)
      = (Path.Homotopic.Quotient.refl x₀).cast rfl γ.source := by
    rw [segTo_zero, Path.Homotopic.Quotient.mk_cast, Path.Homotopic.Quotient.mk_refl]
  rw [UC.mk.injEq]
  refine ⟨γ.source, ?_⟩
  show Path.Homotopic.Quotient.mk (segTo γ 0) ≍ Path.Homotopic.Quotient.refl x₀
  rw [hq]
  exact Path.Homotopic.Quotient.cast_heq rfl γ.source

/-- `UC.segPt γ 1` is the point of the cover over the endpoint of `γ` whose class is that of `γ`. -/
theorem UC.segPt_one {x : X} (γ : Path x₀ x) :
    UC.segPt γ 1 = (⟨x, Path.Homotopic.Quotient.mk γ⟩ : UC x₀) := by
  have hq : Path.Homotopic.Quotient.mk (segTo γ 1)
      = (Path.Homotopic.Quotient.mk γ).cast rfl γ.target := by
    rw [segTo_one, Path.Homotopic.Quotient.mk_cast]
  rw [UC.mk.injEq]
  refine ⟨γ.target, ?_⟩
  show Path.Homotopic.Quotient.mk (segTo γ 1) ≍ Path.Homotopic.Quotient.mk γ
  rw [hq]
  exact Path.Homotopic.Quotient.cast_heq rfl γ.target

end Basics

section Cover

variable {X : Type*} [TopologicalSpace X] [T2Space X] {x₀ : X}

/-- The initial-segment map `t ↦ UC.segPt γ t` is the unique lift of `γ` starting at the base
point of the universal cover. -/
theorem liftPath_segPt (hB : HasDiscBasis X) {x : X} (γ : Path x₀ x)
    (hcont : Continuous (UC.segPt γ))
    (h0 : γ.toContinuousMap 0 = UC.proj (UC.base x₀)) :
    (UC_isCoveringMap_proj (x₀ := x₀) hB).liftPath γ.toContinuousMap (UC.base x₀) h0
      = ⟨UC.segPt γ, hcont⟩ := by
  refine Eq.symm ?_
  refine ((UC_isCoveringMap_proj (x₀ := x₀) hB).eq_liftPath_iff'
    (γ := γ.toContinuousMap) (e := UC.base x₀) h0).mpr ⟨?_, ?_⟩
  · funext t; rfl
  · simpa using UC.segPt_zero γ

/-- Monodromy of the universal cover at the base fibre: a loop class `ζ` sends the base point to
the point over `x₀` whose class is `ζ`. -/
theorem monodromy_base (hB : HasDiscBasis X)
    (hcont : ∀ {x : X} (γ : Path x₀ x), Continuous (UC.segPt γ))
    (ζ : Path.Homotopic.Quotient x₀ x₀) :
    (UC_isCoveringMap_proj (x₀ := x₀) hB).monodromy ζ ⟨UC.base x₀, rfl⟩
      = ⟨⟨x₀, ζ⟩, rfl⟩ := by
  rcases ζ with ⟨γ₀⟩
  show (UC_isCoveringMap_proj (x₀ := x₀) hB).monodromy (Path.Homotopic.Quotient.mk γ₀)
      ⟨UC.base x₀, rfl⟩ = ⟨⟨x₀, Path.Homotopic.Quotient.mk γ₀⟩, rfl⟩
  simp only [IsCoveringMap.monodromy, Path.Homotopic.Quotient.mk]
  refine Subtype.ext ?_
  show (UC_isCoveringMap_proj (x₀ := x₀) hB).liftPath γ₀.toContinuousMap (UC.base x₀) _ 1
      = ⟨x₀, Path.Homotopic.Quotient.mk γ₀⟩
  rw [liftPath_segPt hB γ₀ (hcont γ₀)]
  exact UC.segPt_one γ₀

end Cover

theorem UC_subsingleton_hom_to_real {X : Type*} [TopologicalSpace X] [T2Space X]
    [PathConnectedSpace X] {x₀ : X} (hB : HasDiscBasis X) :
    Subsingleton (Additive (FundamentalGroup (UC x₀) (UC.base x₀)) →+ ℝ) := by
  have hcov : IsCoveringMap (UC.proj (x₀ := x₀)) := UC_isCoveringMap_proj hB
  have hcont : ∀ {x : X} (γ : Path x₀ x), Continuous (UC.segPt γ) :=
    fun γ => UC_continuous_segPt γ hB
  -- Projecting a loop of the cover gives a loop of `X` which is null-homotopic.
  have key : ∀ γ : Path (UC.base x₀) (UC.base x₀),
      Path.Homotopic.Quotient.mk (γ.map hcov.continuous) = Path.Homotopic.Quotient.refl x₀ := by
    intro γ
    set ζ : Path.Homotopic.Quotient x₀ x₀ :=
      Path.Homotopic.Quotient.mk (γ.map hcov.continuous) with hζ
    have hmap : ζ = (Path.Homotopic.Quotient.mk γ).map
        ⟨UC.proj (x₀ := x₀), hcov.continuous⟩ := by
      rw [hζ]; rfl
    -- `ζ` fixes the base point of the fibre because its lift is `γ` itself.
    have h₁ : hcov.monodromy ζ ⟨UC.base x₀, rfl⟩ = ⟨UC.base x₀, rfl⟩ := by
      rw [hmap]
      exact IsCoveringMap.monodromy_map hcov (Path.Homotopic.Quotient.mk γ)
    -- the monodromy moves the base point to the point whose class is `ζ`
    have h₂ : hcov.monodromy ζ ⟨UC.base x₀, rfl⟩ = ⟨⟨x₀, ζ⟩, rfl⟩ :=
      monodromy_base hB hcont ζ
    have h₃ : (⟨x₀, ζ⟩ : UC x₀) = UC.base x₀ := by
      have hh := congrArg Subtype.val (h₂.symm.trans h₁)
      simpa using hh
    have h₄ : ζ = Path.Homotopic.Quotient.refl x₀ := by
      have h₃' : (⟨x₀, ζ⟩ : UC x₀) = ⟨x₀, Path.Homotopic.Quotient.refl x₀⟩ := by
        simpa [UC.base] using h₃
      rw [UC.mk.injEq] at h₃'
      exact eq_of_heq h₃'.2
    simpa [hζ] using h₄
  -- hence every loop of the cover at the base point is null-homotopic
  have hsub : Subsingleton (FundamentalGroup (UC x₀) (UC.base x₀)) := by
    have hall : ∀ γ : Path (UC.base x₀) (UC.base x₀),
        Path.Homotopic γ (Path.refl (UC.base x₀)) := by
      intro γ
      have hinj := IsCoveringMap.injective_path_homotopic_map hcov (UC.base x₀) (UC.base x₀)
      refine Path.Homotopic.Quotient.eq.mp (hinj ?_)
      show (Path.Homotopic.Quotient.mk γ).map ⟨UC.proj (x₀ := x₀), hcov.continuous⟩
        = (Path.Homotopic.Quotient.mk (Path.refl (UC.base x₀))).map
            ⟨UC.proj (x₀ := x₀), hcov.continuous⟩
      rw [← Path.Homotopic.Quotient.mk_map γ ⟨UC.proj (x₀ := x₀), hcov.continuous⟩,
        ← Path.Homotopic.Quotient.mk_map (Path.refl (UC.base x₀))
          ⟨UC.proj (x₀ := x₀), hcov.continuous⟩]
      rw [key γ]
      have hrm : (Path.refl (UC.base x₀)).map hcov.continuous = Path.refl x₀ := by
        ext t; rfl
      rw [hrm]
      exact (Path.Homotopic.Quotient.mk_refl x₀).symm
    refine ⟨fun a b => ?_⟩
    rcases a with ⟨p⟩
    rcases b with ⟨q⟩
    exact Path.Homotopic.Quotient.eq.mpr ((hall p).trans (hall q).symm)
  haveI := hsub
  exact ⟨fun f g => AddMonoidHom.ext fun a => by
    rw [Subsingleton.elim a 0, map_zero, map_zero]⟩

end Work.EQ.UnivCover
