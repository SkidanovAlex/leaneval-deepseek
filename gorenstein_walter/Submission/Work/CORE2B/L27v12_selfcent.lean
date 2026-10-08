import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.oddCore_odd
import Submission.Work.CORE2B.HallAux
import Submission.Work.CORE2B.HallPerPrime_pi_helpers
import Submission.Work.CORE2B.fittingIn_U_normalizer
import Submission.Work.CORE2B.L27cf_helpers
import Submission.Work.Utils.OrderSplit.two_prime_split
import Submission.Work.CORE2B.L27v12_oddpart_mem_fittingU
import Submission.Work.CORE2B.L27v12_twopart_mem_pCoreIn_Hhat

namespace Work.CORE2B

open Subgroup

set_option linter.unusedVariables false

/-- `F(K) ≤ F*(K)`: the Fitting subgroup is one of the two factors of `F*(K) = F(K) E(K)`. -/
theorem fittingIn_le_fstarIn {G : Type} [Group G] (K : Subgroup G) :
    Work.GW2.fittingIn K ≤ Work.GW2.fstarIn K :=
  Subgroup.map_mono le_sup_left

-- Leaf N2 of the lead's design pass 12 (`_design_gw/Core12L27.lean`): `M ⊓ F(U)` is
-- self-centralizing in `F(U)`.
-- Route: `hD.rel` gives `X ≤ F(Ĥ)` with `N_G(X) ⊓ F*(Ĥ) ≤ M`; for `c ∈ F(U)` centralizing
-- `M ⊓ F(U)` and `x ∈ X`, write `x = x₂ · x_{2'}` in the nilpotent `F(Ĥ)`: the `2'`-part lies in
-- `X ⊓ F(U) ≤ F(U) ⊓ N_G(X) ≤ M ⊓ F(U)` (hence is centralized by `c`) and the `2`-part lies in
-- `O₂(Ĥ) = S ⊓ C(U) ≤ C(U) ∋ c` (Theorem 2.6, `h26`); so `c` centralizes `X`, hence
-- `c ∈ N_G(X) ⊓ F*(Ĥ) ≤ M` and `c ∈ F(U) ≤ F(Ĥ) ≤ F*(Ĥ)` give `c ∈ M ⊓ F(U)`.
theorem L27v12_selfcent (T : Work.GW2.LocalToolkit) (h26 : Work.GW2.Thm26Prop)
    (G : Type) [Group G] [Finite G] (hFT : Work.GW2.FeitThompsonProp)
    (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (M : Subgroup G)
    (hD : Work.CORE2B.L27Hyp B M) :
    Work.GW2.fittingIn B.U ⊓
        Subgroup.centralizer ((M ⊓ Work.GW2.fittingIn B.U : Subgroup G) : Set G) ≤
      M ⊓ Work.GW2.fittingIn B.U := by
  -- `F(U) ≤ F(Ĥ)`: `U = O(Ĥ) ◁ Ĥ` by Theorem 2.6.
  have hFU : Work.GW2.fittingIn B.U ≤ Work.GW2.fittingIn B.Hhat :=
    fittingIn_U_le_fittingIn_Hhat h26 G hFT hCtx B
  -- the `2`-part of an element of `F(Ĥ)` lies in `O₂(Ĥ)`, the `2'`-part in `F(U)`
  have hsplit : ∀ x : G, ∃ x2 x2' : G, x = x2 * x2' ∧ x2 ∈ Subgroup.zpowers x ∧
      x2' ∈ Subgroup.zpowers x ∧ (∃ k : ℕ, orderOf x2 = 2 ^ k) ∧ Odd (orderOf x2') :=
    fun x => Utils.OrderSplit.two_prime_split x
  intro c hc
  rw [Subgroup.mem_inf] at hc
  obtain ⟨hcF, hcC⟩ := hc
  rw [Subgroup.mem_inf]
  -- the witness `X ≤ F(Ĥ)` of the relation `Ĥ ⇝ M`; `N_G(X) ⊓ F*(Ĥ) ≤ M`
  obtain ⟨X, hXle, hXN⟩ := hD.rel
  -- `c ∈ F(Ĥ) ≤ F*(Ĥ)` and `c ∈ F(U) ≤ U`
  have hcFH : c ∈ Work.GW2.fittingIn B.Hhat := hFU hcF
  have hcFstar : c ∈ Work.GW2.fstarIn B.Hhat := fittingIn_le_fstarIn B.Hhat hcFH
  have hcU : c ∈ B.U := (Work.CORE2B.in_le_self B.U 2 B.pi).2.2.1 hcF
  -- Theorem 2.6: `O₂(Ĥ) = S ⊓ C(U)` centralizes `U`
  have hO2C : Work.GW2.pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) := by
    rw [← (h26 G hFT hCtx B).2.1]
    exact inf_le_right
  -- it suffices that `c` centralizes `X`
  have hcen : c ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨x2, x2', hxeq, hx2z, hx2'z, ⟨k, hx2ord⟩, hx2'odd⟩ := hsplit x
    have hx2X : x2 ∈ X := (Subgroup.zpowers_le.mpr hx) hx2z
    have hx2'X : x2' ∈ X := (Subgroup.zpowers_le.mpr hx) hx2'z
    have hx2FH : x2 ∈ Work.GW2.fittingIn B.Hhat := hXle hx2X
    have hx2'FH : x2' ∈ Work.GW2.fittingIn B.Hhat := hXle hx2'X
    -- the `2`-part is a 2-element of `F(Ĥ)`, hence lies in `O₂(Ĥ) ≤ C(U) ∋ c`
    have hx2O2 : x2 ∈ Work.GW2.pCoreIn 2 B.Hhat :=
      L27v12_twopart_mem_pCoreIn_Hhat G B hx2FH hx2ord
    have hcomm2 : c * x2 = x2 * c :=
      (Subgroup.mem_centralizer_iff.mp (hO2C hx2O2)) c hcU
    -- the `2'`-part is an odd element of `F(Ĥ)`, hence lies in `F(U)`; as it also lies in `X`,
    -- it is centralized by `c` (it is in `M ⊓ F(U)`)
    have hx2'FU : x2' ∈ Work.GW2.fittingIn B.U :=
      L27v12_oddpart_mem_fittingU h26 G hFT hCtx B hx2'FH hx2'odd
    have hx2'Fstar : x2' ∈ Work.GW2.fstarIn B.Hhat :=
      fittingIn_le_fstarIn B.Hhat (hFU hx2'FU)
    have hx2'M : x2' ∈ M := hXN ⟨Subgroup.le_normalizer hx2'X, hx2'Fstar⟩
    have hx2'MC : x2' ∈ M ⊓ Work.GW2.fittingIn B.U := ⟨hx2'M, hx2'FU⟩
    have hcomm2' : c * x2' = x2' * c :=
      ((Subgroup.mem_centralizer_iff.mp hcC) x2' hx2'MC).symm
    have h3 : Commute c (x2 * x2') := Commute.mul_right hcomm2 hcomm2'
    rw [hxeq]
    exact h3.eq.symm
  have hcN : c ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.centralizer_le_normalizer (X : Set G) hcen
  exact ⟨hXN ⟨hcN, hcFstar⟩, hcF⟩

end Work.CORE2B
