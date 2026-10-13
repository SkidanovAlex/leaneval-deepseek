import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.RowAdzCore

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

-- The `A · D_z f` slot row of the level-six `N₀`-pairing, with the SEPARABLE σ-decay
-- hypothesis on the coefficient.  For the intended `A = c₂ₘ(θ)·L₁₂(F_*)(z)` one has
-- `|D_θ^i c₂ₘ| ≤ 100000·sin(2θ)²` (`Work.FTS.StrongPersist.dthU_c2m_bound6`) and
-- `|D_z^j L₁₂(F_*)| ≤ Cα` (`Work.FTS.StrongPersist.c2mSix_bound_z` with `k = 0` together with
-- `FstarPkg.eqOn_L12_invH`), so the hypothesis holds with `K = Cα` and there is NO
-- `α`-threshold.  (This is strictly stronger than the `Abnd` hypothesis of
-- `H6Pair6Aux.T45AslotLe`, and unlike the σ-free hypothesis of `H6Pair6Aux.H6N0Aux.row_A_dz`
-- it makes every slot provable: the coefficient hypothesis is precisely the extra input that
-- was missing in `H6N0Aux/NOTES_commPiece_FALSE.md`.)
--
-- ROUTE.  `Submission/Work/FTS/StrongPersist/H6Pair6Aux/H6N0Aux/rowA_aux.lean` contains a
-- complete assembly of this row for the σ-free hypothesis.  NOTE: that module does NOT build
-- (it imports `H6N0Aux/commPiece.lean`, which fails to elaborate on a bare `π`, and whose
-- statement is FALSE).  Do NOT import it: COPY its contents into your own file
-- (`rowA_piece`, `rowA_mixed_succ_eq`, `rowA_piece_expansion`, and the Fubini + integrability
-- + binomial-summation assembly of `rowA_core`) and replace its two per-slot lemmas
-- (`rowA_lead_bound`, `rowA_piece_integrable`/`rowA_piece_bound`) by the case analysis below.
--
-- The Leibniz expansion is
--   `mixed b a (A · D_z f) = Σ_{i≤a} Σ_{j≤b} C(a,i)C(b,j)·(mixed j i A)·(mixed (b-j+1)(a-i) f)`
-- on the open quadrant (`TransportS.mixed_mul_Dz_open`), so each slot is `∫_z∫_θ ρ·X·G·H`
-- with `X := mixed j i A`, `G := mixed (b-j+1)(a-i) f`, `H := mixed b a f`.  Write
-- `σ := sin 2θ`, `w := Spaces.w`.  `IsLeafW α a ρ` gives `ρ ≤ w²σ^{-γ}` on the open quadrant
-- (with `η = 0.99 ≤ γ = 1+α/10`, and `leafGam` only when `a ≥ 1`).
--
-- * `(i,j) = (0,0)` (the only slot seeing the level-seven slot `mixed (b+1) a f`, order
--   `a+b+1 ≤ 7`): use `H6Pair6Aux.H6N0Aux.leadPiece` + `H6Pair6Aux.H6N0Aux.dzSelfA2d`
--   verbatim (they need only `|A| ≤ K`, which is `hAbd` at `i = 0` as the factor there is `1`);
--   gives `≤ 5K·HkSq α 6 f` and the integrability of the slot.
-- * `i = 0`, `j ≥ 1`: `X = DzIter j A` with `|X| ≤ K`; `G = mixed (b-j+1) a f` has the SAME
--   angular index `a` as the leaf weight `ρ` and order `a+(b-j+1) ≤ a+b ≤ 6`, and
--   `H = mixed b a f` has order `a+b ≤ 6`; both are dominated by `HkIntegrand α 6 f` with the
--   weight `ρ` via `H6Pair6Aux.T5bPrep.domLeaf_all`.  Then
--   `2|G||H| ≤ G²+H²` gives `|∫∫ρXGH| ≤ K·HkSq α 6 f`.
-- * `i ≥ 1`: `|X| ≤ Kσ`; since `ρ ≤ w²σ^{-γ}` and `σ^{1-γ} = σ^{-α/10} ≤ σ^{-η}` (because
--   `α/10 ≤ 0.1 < 0.99 = η`),
--       `ρ|X||G||H| ≤ K·w²σ^{-η}|G||H| ≤ K·(w²σ^{-η}G² + w²σ^{-γ}H²)`   pointwise
--   (`2ab ≤ a²+b²` with `σ^{-η}, σ^{-γ} ≥ 1`).  Both integrals are `≤ HkSq α 6 f` by
--   `H6Pair6Aux.intSlotLeHkSq α hm6`: `G` has order `(a-i)+(b-j+1) ≤ 6`, and `H` has `1 ≤ a`
--   with `a+b ≤ 6`; use the FIRST conjunct with `θw := σ^{-η}` in the case `a-i = 0` (then `G`
--   is a pure radial slot) and the SECOND conjunct with `θw := σ^{-η}` resp. `θw := σ^{-γ}`
--   when `a-i ≥ 1` resp. for `H`.  Hence `≤ 2K·HkSq α 6 f`; the same domination gives the
--   integrability of the slot (`HkIntegrand α 6 f` is integrable by `hm6`).
-- * Fubini and `Σ_{i≤a}Σ_{j≤b} C(a,i)C(b,j) = 2^a2^b ≤ 64` then give
--   `≤ (2·64+5)K·HkSq α 6 f ≤ 133·K·α^{-3}(1+Xn α f)^4(1+HkSq α 6 f)` (`α^{-3} ≥ 1`,
--   `(1+Xn)^4 ≥ 1`, `1+HkSq ≥ HkSq`), so any `C ≥ 133` works.
theorem RowAdz : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f A : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ) (K : ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkMem α 7 f →
      Work.FTS.EllipticEst.SmoothOpen A → 0 ≤ K →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ j i : ℕ, i + j ≤ 6 →
        |Work.Spaces.mixed j i A z θ| ≤ K * (if i = 0 then 1 else Real.sin (2 * θ))) →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => A z θ * Work.Spaces.Dz f z θ) f|
        ≤ C * K * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f) := by
  refine ⟨400, by norm_num, ?_⟩
  intro α hα f A a b ρ K hso hm6 hm7 hAso hK hAbd hab hρ
  exact (rowA_core hα.1 hα.2 hK hso hAso hm6 hm7 hρ hAbd hab).trans
    (rowA_majorant hα.1 hα.2 hK)

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
