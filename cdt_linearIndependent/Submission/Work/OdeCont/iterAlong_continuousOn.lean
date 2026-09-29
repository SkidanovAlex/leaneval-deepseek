import Mathlib
import Submission.Work.OdeCont.defs

namespace Work.OdeCont

theorem iterAlong_continuousOn {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (F : ℂ → V → V) (z₀ : ℂ) (y : V) (S : Set ℂ)
    (hS : Convex ℝ S) (hz₀ : z₀ ∈ S)
    (hGcont : ∀ n, ContinuousOn (fun w => F w (iter F z₀ y n w)) S)
    (n : ℕ) (z : ℂ) (hz : z ∈ S) :
    ContinuousOn (fun t : ℝ => F (z₀ + t • (z - z₀)) (iter F z₀ y n (z₀ + t • (z - z₀)))) (Set.Icc 0 1) := by
  have hγ : ContinuousOn (fun t : ℝ => z₀ + t • (z - z₀)) (Set.Icc 0 1) := by fun_prop
  refine (hGcont n).comp hγ ?_
  intro t ht
  have h1 : (0:ℝ) ≤ 1 - t := by linarith [ht.2]
  have h2 : (0:ℝ) ≤ t := ht.1
  have hmem := hS (x := z₀) (y := z) (a := 1 - t) (b := t) hz₀ hz h1 h2 (by ring)
  have heq : (1 - t) • z₀ + t • z = z₀ + t • (z - z₀) := by
    rw [sub_smul, one_smul]; module
  rwa [heq] at hmem

end Work.OdeCont
