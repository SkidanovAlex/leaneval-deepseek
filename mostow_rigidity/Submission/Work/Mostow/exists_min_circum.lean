import Mathlib
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.Hyper

namespace Work.Mostow

open Submission.Mostow

/-- For a compact nonempty set `K`, the circumradius function `x ↦ sSup (hdist x · '' K)` attains its
minimum: there is a circumcentre `c`. -/
theorem exists_min_circum (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n)
    {K : Set (Submission.Mostow.E n)} (hKc : IsCompact K) (hKn : K.Nonempty) :
    ∃ c : Submission.Mostow.E n, ∀ x : Submission.Mostow.E n,
      sSup ((fun v : Submission.Mostow.E n => Submission.Mostow.hdist c v) '' K) ≤
        sSup ((fun v : Submission.Mostow.E n => Submission.Mostow.hdist x v) '' K) := by
  unfold Submission.Mostow.HypIsometryProp at hI
  obtain ⟨hnn, hsym, hziff, htri, hcont, hcompact, _⟩ := hI
  -- circumradius function
  set f : E n → ℝ := fun x => sSup ((fun v : E n => hdist x v) '' K) with hfdef
  -- it is continuous, being the supremum over the compact set `K` of a jointly continuous kernel
  have hfcont : Continuous f := by
    have h : Continuous fun x : E n => sSup ((fun v : E n => hdist x v) '' K) :=
      hKc.continuous_sSup (f := fun (x : E n) (v : E n) => hdist x v) hcont
    simpa only [f] using h
  obtain ⟨v₀, hv₀⟩ := hKn
  -- the image of `K` under `v ↦ hdist x v` is bounded above (it is compact)
  have hcbd : ∀ x : E n, BddAbove ((fun v : E n => hdist x v) '' K) := fun x =>
    hKc.bddAbove_image ((hcont.comp (Continuous.prodMk_right x)).continuousOn)
  have hM0 : 0 ≤ f 0 := by
    have h1 : hdist (0 : E n) v₀ ≤ f 0 := le_csSup (hcbd 0) (Set.mem_image_of_mem _ hv₀)
    exact le_trans (hnn 0 v₀) h1
  -- the superlevel set `{x | f x ≤ f 0}` is contained in the compact set below
  have hT : IsCompact {x : E n | hdist (0 : E n) x ≤ f 0 + hdist (0 : E n) v₀} :=
    hcompact 0 (f 0 + hdist (0 : E n) v₀)
  have hmem0 : (0 : E n) ∈ {x : E n | hdist (0 : E n) x ≤ f 0 + hdist (0 : E n) v₀} := by
    simp only [Set.mem_ofPred_eq]
    have hz : hdist (0 : E n) 0 = 0 := (hziff 0 0).2 rfl
    have hv : 0 ≤ hdist (0 : E n) v₀ := hnn 0 v₀
    linarith
  obtain ⟨c, hcmin0⟩ := hT.exists_isMinOn ⟨0, hmem0⟩ hfcont.continuousOn
  have hcmin : ∀ x ∈ {x : E n | hdist (0 : E n) x ≤ f 0 + hdist (0 : E n) v₀}, f c ≤ f x :=
    Filter.eventually_principal.mp hcmin0.2
  refine ⟨c, fun x => ?_⟩
  -- `c` minimises `f` on the compact set; outside it `hdist x v₀ > f 0 ≥ f c`
  have hgoal : f c ≤ f x := by
    by_cases hx : x ∈ {x : E n | hdist (0 : E n) x ≤ f 0 + hdist (0 : E n) v₀}
    · exact hcmin x hx
    · have hx' : f 0 + hdist (0 : E n) v₀ < hdist (0 : E n) x := by
        simpa only [Set.mem_ofPred_eq, not_le] using hx
      have hfc0 : f c ≤ f 0 := hcmin 0 hmem0
      have hfx : hdist x v₀ ≤ f x := le_csSup (hcbd x) (Set.mem_image_of_mem _ hv₀)
      have htri' : hdist (0 : E n) x ≤ hdist (0 : E n) v₀ + hdist v₀ x := htri 0 v₀ x
      have hsym' : hdist v₀ x = hdist x v₀ := hsym v₀ x
      have h2 : f 0 < hdist x v₀ := by linarith
      linarith
  exact hgoal

end Work.Mostow
