/-
# Continuity of the chain integral in the parameter (B1a, node N5 support)

For a polygonal chain `L` and a jointly continuous family `(w, ζ) ↦ g w ζ` on `U ×ˢ chainTrace L`,
the function `w ↦ chainIntegral (fun ζ => g w ζ) L` is continuous on `U`.

The mathematical content is entirely in the one-segment case: a segment integral is an interval
integral `∫ t in 0..1, (g w (a + t (b-a))) * (b-a)`, and a parameterized integral of a function
that is jointly continuous on `U ×ˢ Icc 0 1` is continuous in the parameter
(`Work.RPB.B1a.continuousOn_intervalIntegral`).  The chain statement then follows by induction,
using that the trace of the tail of a chain is contained in the trace of the chain.
-/
import Mathlib
import Submission.Work.RPB.B1a.SegChain
import Submission.Work.RPB.B1a.continuousOn_intervalIntegral

namespace Work.RPB.B1a

open Complex Set MeasureTheory intervalIntegral Function
open scoped Topology

noncomputable section

/-- The integral of `g w` along a single segment depends continuously on `w ∈ U`, as long as the
family `(w, ζ) ↦ g w ζ` is jointly continuous on `U ×ˢ segment ℝ a b`. -/
lemma continuousOn_segIntegral {U : Set ℂ} {a b : ℂ} {g : ℂ → ℂ → ℂ}
    (hjoint : ContinuousOn (fun p : ℂ × ℂ => g p.1 p.2) (U ×ˢ segment ℝ a b)) :
    ContinuousOn (fun w => segIntegral (g w) a b) U := by
  have hF : ContinuousOn (Function.uncurry
      (fun w : ℂ => fun t : ℝ => g w (a + (t : ℂ) * (b - a)) * (b - a)))
      (U ×ˢ Icc (0:ℝ) 1) := by
    have hmap : ContinuousOn (fun p : ℂ × ℝ => (p.1, a + (p.2 : ℂ) * (b - a)))
        (U ×ˢ Icc (0:ℝ) 1) := by
      fun_prop
    have hmaps : MapsTo (fun p : ℂ × ℝ => (p.1, a + (p.2 : ℂ) * (b - a)))
        (U ×ˢ Icc (0:ℝ) 1) (U ×ˢ segment ℝ a b) := by
      rintro ⟨w, t⟩ ⟨hw, ht⟩
      exact ⟨hw, mem_segment_param ht⟩
    have h1 : ContinuousOn (fun p : ℂ × ℝ => g p.1 (a + (p.2 : ℂ) * (b - a)))
        (U ×ˢ Icc (0:ℝ) 1) := by
      simpa only [Function.comp_def] using hjoint.comp hmap hmaps
    exact h1.mul (continuousOn_const (c := b - a))
  have h3 := continuousOn_intervalIntegral zero_le_one hF
  simpa [segIntegral] using h3

theorem continuousOn_chainIntegral {U : Set ℂ} (L : List (ℂ × ℂ)) {g : ℂ → ℂ → ℂ}
    (hjoint : ContinuousOn (fun p : ℂ × ℂ => g p.1 p.2) (U ×ˢ chainTrace L)) :
    ContinuousOn (fun w => chainIntegral (fun ζ => g w ζ) L) U := by
  induction L with
  | nil =>
    simpa [chainIntegral] using continuousOn_const (c := (0 : ℂ)) (s := U)
  | cons s L ih =>
    obtain ⟨a, b⟩ := s
    have h1 : ContinuousOn (fun p : ℂ × ℂ => g p.1 p.2) (U ×ˢ segment ℝ a b) :=
      hjoint.mono (Set.prod_mono_right fun z hz => ⟨(a, b), List.mem_cons_self, hz⟩)
    have h2 : ContinuousOn (fun p : ℂ × ℂ => g p.1 p.2) (U ×ˢ chainTrace L) :=
      hjoint.mono (Set.prod_mono_right fun z hz => by
        obtain ⟨t, ht, hzt⟩ := hz
        exact ⟨t, List.mem_cons_of_mem _ ht, hzt⟩)
    have hh := continuousOn_segIntegral h1
    have ht := ih h2
    have key : ∀ w, chainIntegral (fun ζ => g w ζ) ((a, b) :: L)
        = segIntegral (g w) a b + chainIntegral (g w) L := by
      intro w
      rw [chainIntegral_cons]
    rw [show (fun w => chainIntegral (fun ζ => g w ζ) ((a, b) :: L))
        = fun w => segIntegral (g w) a b + chainIntegral (g w) L from funext key]
    exact hh.add ht

end

end Work.RPB.B1a
