import Mathlib
import Submission.Work.WilE9.Sharp.Vocab
import Submission.Work.WilE9.Psi.psi_psiInv

namespace Work.WilE9.Sharp

/-!
The graph relation for the `ψ`-transport of a stratum: if the graph of `f` is the `psiV`-preimage
of a set `Z`, then any point of `Z` whose last coordinate `τ` lies in the open interval `(-1,1)`
(and whose first `n` coordinates are `psiV x`) is forced to have `τ = ψ (f x)`.

Indeed, `z = Fin.snoc x (psiInv τ)` is the unique point with `psiV z = Fin.snoc (psiV x) τ`; since
`Fin.snoc (psiV x) τ ∈ Z`, we get `z ∈ graphOf f`, hence `psiInv τ = f x`, and applying `ψ` gives
the claim.
-/

/-- `psiV` commutes with `Fin.snoc`: appending a last coordinate to the argument appends its `ψ`. -/
theorem psiV_snoc {n : ℕ} (x : Fin n → ℝ) (a : ℝ) :
    WilkiesDesign.E.psiV (Fin.snoc x a) =
      Fin.snoc (WilkiesDesign.E.psiV x) (WilkiesDesign.E.psi a) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp [WilkiesDesign.E.psiV, Fin.snoc_last]
  · intro j
    simp [WilkiesDesign.E.psiV, Fin.snoc_castSucc]

theorem graph_rel {n : ℕ} {f : (Fin n → ℝ) → ℝ} {Z : Set (Fin (n + 1) → ℝ)}
    (hZ : WilkiesDesign.graphOf f = WilkiesDesign.E.psiV ⁻¹' Z) {x : Fin n → ℝ} {τ : ℝ}
    (hτ : |τ| < 1) (h : Fin.snoc (WilkiesDesign.E.psiV x) τ ∈ Z) :
    τ = WilkiesDesign.E.psi (f x) := by
  -- `ψ (ψInv τ) = τ` since `|τ| < 1`.
  have hψ : WilkiesDesign.E.psi (Work.WilE9.psiInv τ) = τ :=
    Work.WilE9.Psi.psi_psiInv τ hτ
  -- the point of `ℝⁿ⁺¹` whose `psiV`-image is `Fin.snoc (psiV x) τ`
  set z : Fin (n + 1) → ℝ := Fin.snoc x (Work.WilE9.psiInv τ) with hzdef
  -- `psiV z = Fin.snoc (psiV x) τ`
  have hpsiV : WilkiesDesign.E.psiV z = Fin.snoc (WilkiesDesign.E.psiV x) τ := by
    rw [hzdef, psiV_snoc, hψ]
  -- so `z` lies in the `psiV`-preimage of `Z`, i.e. in the graph of `f`.
  have hmem : z ∈ WilkiesDesign.graphOf f := by
    rw [hZ]
    simp only [Set.mem_preimage]
    rw [hpsiV]
    exact h
  -- reading off the graph relation at the last coordinate
  have hz : z (Fin.last n) = f (Fin.init z) := hmem
  rw [hzdef, Fin.init_snoc, Fin.snoc_last] at hz
  calc τ = WilkiesDesign.E.psi (Work.WilE9.psiInv τ) := hψ.symm
    _ = WilkiesDesign.E.psi (f x) := by rw [hz]

end Work.WilE9.Sharp
