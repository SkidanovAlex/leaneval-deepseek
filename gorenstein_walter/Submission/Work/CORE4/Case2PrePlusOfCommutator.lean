import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2KB0
import Submission.Work.CORE4.Case2SevenAux
import Submission.Work.CORE4.Case2K1_ne_bot
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE2A.exists_mul_of_notMem_of_relIndex_eq_two
import Submission.Work.CORE4.Case2SNotMemS0
import Submission.Work.CORE4.Case2SingleCommutator
import Submission.Work.CORE4.Case2KOddCommutator

namespace Work.CORE4

open Work.GW2 Subgroup
open scoped commutatorElement

/-- `S` normalises `U ⊓ M`: `S ≤ M` and `S ≤ H`, and `U ⊓ M ⊴ M ⊓ H`. -/
theorem Case2SLeNormUinfM {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (h : Work.GW2.Case2Ctx B) :
    (B.S : Subgroup G) ≤ Subgroup.normalizer ((B.U ⊓ h.D.M : Subgroup G) : Set G) := by
  have hle : (B.U ⊓ h.D.M) ≤ h.D.M ⊓ B.H :=
    le_inf inf_le_right (le_trans inf_le_left B.U_le_H)
  have hnorm : h.D.M ⊓ B.H ≤ Subgroup.normalizer ((B.U ⊓ h.D.M : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp
      (Work.GW2.Case2Ctx.U_inf_M_normal (B := B) h)
  exact le_trans (le_inf h.S_le_M B.S_le_H) hnorm

/-- If `s ∉ S₀`, then every `g ∈ S \ S₀` is `s * x` with `x ∈ S₀` (the complement of the
index-two subgroup `S₀` is a single coset). -/
theorem Case2SCosetRep {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (h : Work.GW2.Case2Ctx B) (hs : h.D.s ∉ B.S0) :
    ∀ g ∈ (B.S : Subgroup G), g ∉ B.S0 → ∃ x ∈ B.S0, g = h.D.s * x :=
  fun g hgS hg0 => Work.CORE2A.exists_mul_of_notMem_of_relIndex_eq_two
    (S := (B.S : Subgroup G)) (S0 := B.S0) B.S0_index h.D.s_mem_S hs hgS hg0

/-! ## The three delegated pieces

`Case2KOddCommutator` (`K ≤ [S, U ⊓ M]`), `Case2SingleCommutator` (`[⟨s⟩, U ⊓ M] ≤ K`) and
`Case2SNotMemS0` (`s ∉ S₀`) are the three group-theoretic inputs of the argument below; they
live in the sibling modules imported above. -/

/-- Bender 1981, §4 (1) (p. 224), reduced to its group-theoretic core.

`Case2Ctx.nine` gives `S ≤ E(M) = layerIn h.D.M`, so `S ⊓ E(M) = S`; Bender's (1)
`K = [S ∩ E, U ∩ M] = I_{U∩M}(s)` therefore reads `K = [S, U ⊓ M]`.  The inclusion
`K ≤ [S, U ⊓ M]` and the piece `[⟨s⟩, U ⊓ M] ≤ K` are elementary: for `k ∈ K` one has
`⁅s, k⁆ = k⁻²`, and since `K` has odd order the squaring map on `K` is onto, so
`k = (k^m)² = ⁅s, k^m⁆⁻¹ ∈ [S, U ⊓ M]` for `m = (|K| + 1)/2`.  Conversely `S = S₀ ⊔ ⟨s⟩`
because `s ∉ S₀` (if `s ∈ S₀` then `s = B.t` since `S₀` is cyclic of index two and hence has the
unique involution `t = B.t`; then `K = I_{U⊓M}(t) = ⊥` since `U ⊓ M ≤ C_G(t)`, contradicting
`K ≠ ⊥` from `Submission.Work.CORE4.Case2K1_ne_bot`).

What remains is precisely the inclusion for the *cyclic* part: `[S₀, U ⊓ M] ≤ K` (equivalently
`[S₀, U ⊓ M] ≤ I_{U⊓M}(s)`, i.e. `S₀` inverts `K`), which is Bender's "`S ∩ E/Z(E)` is cyclic and
inverted by `s`" and is isolated here as a hypothesis. -/
theorem Case2PrePlusOfCommutator :
    ∀ (G : Type) [Group G] [Finite G] (I : Work.GW2.C4Inputs), Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ⁅B.S0, B.U ⊓ h.D.M⁆ ≤ h.D.K →
        h.D.K = ⁅(B.S : Subgroup G) ⊓ Work.GW2.layerIn h.D.M, B.U ⊓ h.D.M⁆ := by
  intro G _ _ I hbc B h hhyp
  obtain ⟨p, k, hp, hpodd, h7, hiso, hSE⟩ := h.nine
  -- `S ≤ E(M)`, so `S ⊓ E(M) = S`
  have hSinfE : (B.S : Subgroup G) ⊓ Work.GW2.layerIn h.D.M = (B.S : Subgroup G) :=
    inf_eq_left.mpr hSE
  rw [hSinfE]
  have hS_norm : (B.S : Subgroup G) ≤
      Subgroup.normalizer ((B.U ⊓ h.D.M : Subgroup G) : Set G) := Case2SLeNormUinfM B h
  have hs_not : h.D.s ∉ B.S0 := Case2SNotMemS0 I hbc h
  refine le_antisymm ?_ ?_
  · -- `K ≤ [S, U ⊓ M]`
    exact Case2KOddCommutator B h
  · -- `[S, U ⊓ M] ≤ K`
    rw [Subgroup.commutator_le]
    intro g hgS n hnN
    by_cases hg0 : g ∈ B.S0
    · exact (Subgroup.commutator_le.mp hhyp) g hg0 n hnN
    · obtain ⟨x, hx0, hgx⟩ := Case2SCosetRep B h hs_not g hgS hg0
      rw [hgx]
      -- `x * n * x⁻¹ ∈ U ⊓ M` and both factors of the commutator identity lie in `K`
      have hxn : x * n * x⁻¹ ∈ B.U ⊓ h.D.M :=
        (Subgroup.le_normalizer_iff.mp hS_norm) x (B.S0_le hx0) n hnN
      have h1 : ⁅h.D.s, x * n * x⁻¹⁆ ∈ h.D.K := by
        simpa only [commutatorElement_def] using
          Case2SingleCommutator B h hS_norm (x * n * x⁻¹) hxn
      have h2 : ⁅x, n⁆ ∈ h.D.K := (Subgroup.commutator_le.mp hhyp) x hx0 n hnN
      have hid : ⁅h.D.s * x, n⁆ = ⁅h.D.s, x * n * x⁻¹⁆ * ⁅x, n⁆ := by
        simp only [commutatorElement_def]
        group
      rw [hid]
      exact h.D.K.mul_mem h1 h2

end Work.CORE4
