/-
  `Work.CoreStep.stratReindex_exists`: reindexing an ambient stratum along an equivalence
  `e : Fin (0 + N) ≃ Fin (0 + N')` of coordinate sets.

  The witness is `Work.CoreStep.Stratum.reindex e S` (see `StratReindexDefs.lean`): the
  semi-Pfaffian set is reindexed and the equations are renamed, both along `e`.

  The three non-elementary ingredients are proved separately and imported here:

  * `Work.CoreStep.stratReindex_good_fwd`, `...good_bwd` : `Good (reindex e S) ↔ Good S`
    (the `p = 0` case, where the fibre condition of `Good` is vacuous, so an arbitrary
    coordinate permutation is harmless; the rank condition survives because reindexing
    permutes the columns of the Jacobian matrix);
  * `Work.CoreStep.stratReindex_jac` : the Jacobian of the reindexed stratum at `y` is the
    Jacobian of `S` at `y ∘ e` precomposed with the coordinate equivalence — which is what
    makes the `finrank` of the image of the tangent space under a linear map invariant.
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.CoreStep.ProjTopDefs
import Submission.Work.CoreStep.StratReindexDefs
import Submission.Work.CoreStep.stratReindex_good_fwd
import Submission.Work.CoreStep.stratReindex_good_bwd
import Submission.Work.CoreStep.stratReindex_jac

set_option autoImplicit false
noncomputable section
open Classical WilkiesDesign WilkiesDesign.E

namespace Work.CoreStep

theorem stratReindex_exists {N N' : ℕ} (e : Fin (0 + N) ≃ Fin (0 + N'))
    (S : WilkiesDesign.E.Stratum 0 N) :
    ∃ S' : WilkiesDesign.E.Stratum 0 N', ∃ (hj : S'.j = S.j),
      S'.X.set = {y : Fin (0 + N') → ℝ | (fun i : Fin (0 + N) => y (e i)) ∈ S.X.set} ∧
      S'.deg = S.deg ∧ (WilkiesDesign.E.Stratum.Good S' ↔ WilkiesDesign.E.Stratum.Good S) ∧
      (∀ (y : Fin (0 + N') → ℝ) (a : Fin S.j),
        WilkiesDesign.E.eaEval S'.X.c (S'.h (Fin.cast hj.symm a)) y =
          WilkiesDesign.E.eaEval S.X.c (S.h a) (fun i : Fin (0 + N) => y (e i))) ∧
      ∃ L : (Fin (0 + N) → ℝ) ≃ₗ[ℝ] (Fin (0 + N') → ℝ),
        (∀ (v : Fin (0 + N) → ℝ) (j : Fin (0 + N')), L v j = v (e.symm j)) ∧
        (∀ (y : Fin (0 + N') → ℝ) (k : ℕ) (M : (Fin (0 + N') → ℝ) →ₗ[ℝ] (Fin k → ℝ))
           (M' : (Fin (0 + N) → ℝ) →ₗ[ℝ] (Fin k → ℝ)),
           (∀ v, M (L v) = M' v) →
           Module.finrank ℝ ((LinearMap.ker (Work.WilE7.MainDesign.jac S' y)).map M) =
             Module.finrank ℝ ((LinearMap.ker (Work.WilE7.MainDesign.jac S
               (fun i : Fin (0 + N) => y (e i)))).map M')) := by
  -- the linear equivalence `L : v ↦ v ∘ e.symm` which the final clause is about
  let L : (Fin (0 + N) → ℝ) ≃ₗ[ℝ] (Fin (0 + N') → ℝ) := LinearEquiv.funCongrLeft ℝ ℝ e.symm
  have hLapp : ∀ v : Fin (0 + N) → ℝ, L v = (fun j : Fin (0 + N') => v (e.symm j)) :=
    fun v => rfl
  refine ⟨Stratum.reindex e S, rfl, ?_, ?_, ?_, ?_, L, ?_, ?_⟩
  · exact Stratum.reindex_X_set e S
  · exact Stratum.reindex_deg e S
  · exact ⟨stratReindex_good_fwd e S, stratReindex_good_bwd e S⟩
  · -- the `Fin.cast` of the (definitionally trivial) proof `hj` is the identity
    have hkey : ∀ (hj' : (Stratum.reindex e S).j = S.j) (y : Fin (0 + N') → ℝ)
        (a : Fin S.j),
        eaEval (Stratum.reindex e S).X.c ((Stratum.reindex e S).h (Fin.cast hj'.symm a)) y =
          eaEval S.X.c (S.h a) (fun i : Fin (0 + N) => y (e i)) := by
      intro hj' y a
      have hcast : (Fin.cast hj'.symm a : Fin (Stratum.reindex e S).j) = a := by
        ext
        simp
      rw [hcast]
      exact Stratum.reindex_h_eval e S y a
    intro y a
    exact hkey rfl y a
  · intro v j
    rw [hLapp v]
  · intro y k M M' hM
    have hjac : ∀ v : Fin (0 + N) → ℝ,
        Work.WilE7.MainDesign.jac (Stratum.reindex e S) y (L v)
          = Work.WilE7.MainDesign.jac S (fun i : Fin (0 + N) => y (e i)) v := by
      intro v
      rw [hLapp v]
      exact stratReindex_jac e S y v
    -- the tangent space of the reindexed stratum is the image of the tangent space of `S`
    have hker : (LinearMap.ker (Work.WilE7.MainDesign.jac S
          (fun i : Fin (0 + N) => y (e i)))).map L.toLinearMap
        = LinearMap.ker (Work.WilE7.MainDesign.jac (Stratum.reindex e S) y) := by
      ext w
      rw [Submodule.mem_map]
      constructor
      · rintro ⟨v, hv, rfl⟩
        have hv' : (Work.WilE7.MainDesign.jac S (fun i : Fin (0 + N) => y (e i))) v = 0 := hv
        change (Work.WilE7.MainDesign.jac (Stratum.reindex e S) y) (L v) = 0
        rw [hjac v]
        exact hv'
      · intro hw
        have hw' : (Work.WilE7.MainDesign.jac (Stratum.reindex e S) y) w = 0 := hw
        refine ⟨L.symm w, ?_, ?_⟩
        · change (Work.WilE7.MainDesign.jac S (fun i : Fin (0 + N) => y (e i))) (L.symm w) = 0
          rw [← hjac (L.symm w), LinearEquiv.apply_symm_apply]
          exact hw'
        · simp
    -- ... hence the two `finrank`s agree
    have hmain : (LinearMap.ker (Work.WilE7.MainDesign.jac (Stratum.reindex e S) y)).map M
        = (LinearMap.ker (Work.WilE7.MainDesign.jac S
            (fun i : Fin (0 + N) => y (e i)))).map M' := by
      rw [← hker]
      ext w
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨v, hv, rfl⟩ := hx
        exact ⟨v, hv, (hM v).symm⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨L v, ⟨v, hv, rfl⟩, hM v⟩
    rw [hmain]

end Work.CoreStep
