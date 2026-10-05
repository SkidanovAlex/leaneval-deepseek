import Mathlib
import Submission.Work.RPV.Defs
import Submission.Work.RPB.B1a.SegChain
import Submission.Work.RPB.B1a.Cauchy
import Submission.Work.RPB.B1a.exists_chain_of_isOpen_of_isPreconnected
import Submission.Work.RPB.B1a.continuousOn_dslope_prod
import Submission.Work.RPB.B1a.differentiableOn_chainIntegral_div
import Submission.Work.RPB.B1a.continuousOn_chainIntegral
import Submission.Work.RPB.B1a.isConservativeOn_chainIntegral
import Submission.Work.RPB.B1a.exists_primitive_of_closed_chain_eq_zero

namespace Work.RPB.B1a

open Complex Set MeasureTheory Function Filter
open scoped Topology Filter

noncomputable section



/-- The `dslope`-integral `w ↦ ∫_P dslope f w ζ dζ` of a polygonal chain `P ⊆ U` is holomorphic on
`U`: the integrand is jointly continuous (which gives continuity of the integral and, via Fubini and
the rectangle Cauchy theorem, Morera's rectangle condition). -/
theorem differentiableOn_chainIntegral_dslope {U : Set ℂ} (hUo : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) {L : List (ℂ × ℂ)} (hL : ChainIn U L) :
    DifferentiableOn ℂ (fun w => chainIntegral (fun ζ => dslope f w ζ) L) U := by
  have htrace : chainTrace L ⊆ U := fun z ⟨s, hs, hz⟩ => (hL s hs).2.2 hz
  have hjoint : ContinuousOn (fun p : ℂ × ℂ => dslope f p.1 p.2) (U ×ˢ chainTrace L) :=
    (continuousOn_dslope_prod hUo hf).mono (Set.prod_mono subset_rfl htrace)
  have hhol : ∀ ζ ∈ chainTrace L, DifferentiableOn ℂ (fun w => dslope f w ζ) U := by
    intro ζ hζ
    rw [show (fun w => dslope f w ζ) = dslope f ζ from funext fun w => dslope_comm f w ζ]
    exact (Complex.differentiableOn_dslope (hUo.mem_nhds (htrace hζ))).mpr hf
  exact (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hUo).mp
    ⟨isConservativeOn_chainIntegral L hjoint hhol, continuousOn_chainIntegral L hjoint⟩

/-- **Cauchy's theorem for a closed polygonal chain in `U`**: the integral of a holomorphic function
along a closed chain inside a bounded open set with connected complement vanishes. -/
theorem chainIntegral_eq_zero_of_isChainFrom_self' {U : Set ℂ} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUcc : IsConnected Uᶜ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) {L : List (ℂ × ℂ)} {p : ℂ} (hLc : IsChainFrom p p L)
    (hLin : ChainIn U L) :
    chainIntegral f L = 0 := by
  have htrace : chainTrace L ⊆ U := fun z ⟨s, hs, hz⟩ => (hLin s hs).2.2 hz
  have hcontf : ContinuousOn f (chainTrace L) := hf.continuousOn.mono htrace
  have hN : DifferentiableOn ℂ (fun w => chainIntegral (fun ζ => (ζ - w)⁻¹) L) (chainTrace L)ᶜ := by
    simpa only [one_mul] using
      differentiableOn_chainIntegral_div L
        (continuousOn_const : ContinuousOn (fun _ : ℂ => (1 : ℂ)) (chainTrace L))
  exact chainIntegral_eq_zero_of_isChainFrom_self hUo hUb hUcc hf hLc hLin
    (differentiableOn_chainIntegral_dslope hUo hf hLin)
    (differentiableOn_chainIntegral_div L hcontf) hN

-- Node N5 of the conformal-map route (`RECTPEG_B1_LEAD.md` §3), re-dispatched in-house (TauCeti is
-- not a `require` of this workspace, so its homology-Cauchy result is unavailable; see
-- `Submission/Work/RPB/B1a/IMPORT_BLOCKER.md`).  Content: for a bounded open connected `U ⊆ ℂ` with
-- connected complement, every holomorphic function on `U` has a primitive.  (The same statement is
-- held as a placeholder in `Submission/Work/RPB1a/Held.lean`.)
--
-- Hint (§4 N5): (i) open connected sets are polygonally connected (the set reachable by polygons
-- from a base point is open and closed in `U`); (ii) for a closed polygon `P ⊆ U` and `a ∉ U`:
-- `Uᶜ` is connected, unbounded and disjoint from `P`, hence lies in the unbounded component of
-- `(range P)ᶜ`, so the winding number of `P` about `a` is `0` — use Mathlib's winding-number
-- machinery; (iii) with all winding numbers `0` outside `U`, Cauchy's integral result makes the
-- integral of `f` over every closed polygon vanish, so `g z := ∫` along a polygon from the base
-- point to `z` is well defined; (iv) on a ball inside `U`, `g` differs from a wedge-type integral by
-- a constant, hence `deriv g = f` there (Mathlib has the ball/local primitives results).  The
-- statement is Mathlib-only and needs no new library.  (Checked to elaborate in
-- `B1a/_stmtcheck2.lean`; note `EqOn` must be written `Set.EqOn`.)
lemma hasPrimitives_of_isConnected_compl (U : Set ℂ) (hUo : IsOpen U) (hUc : IsConnected U)
    (hUb : Bornology.IsBounded U) (hUcc : IsConnected Uᶜ) :
    ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ Set.EqOn (deriv g) f U := by
  intro f hf
  exact exists_primitive_of_closed_chain_eq_zero U hUo hUc hf fun p L hc hLin =>
    chainIntegral_eq_zero_of_isChainFrom_self' hUo hUb hUcc hf hc hLin

end

end Work.RPB.B1a
