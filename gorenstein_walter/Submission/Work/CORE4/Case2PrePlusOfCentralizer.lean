import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2KB0
import Submission.Work.CORE4.Case2SevenAux
import Submission.Work.CORE4.Case2CountSetup

namespace Work.CORE4

/-- Bender 1981, §4 (2) (p. 224), reduced to its group-theoretic core.

`Case2Ctx.nine` gives `S ≤ E(M)`, so `S ⊓ E(M) = S`, and `h.D.B0_def` gives
`B₀ = (U ⊓ M) ⊓ C_G(s)`.  Hence Bender's (2) `B = C_{U∩M}(S ∩ E) = C_{U∩M}(s)` reads
`B₀ = (U ⊓ M) ⊓ C_G(S)`:

* `(U ⊓ M) ⊓ C_G(S) ≤ B₀` is immediate, since `s ∈ S`;
* `B₀ ≤ (U ⊓ M) ⊓ C_G(S)` is exactly "`B₀` centralizes `S₀`", i.e. `[S₀, B₀] = 1` (the
  `S₀`-part of the Sylow), which is the content of Bender's (2) and is isolated here as a
  hypothesis `B₀ ≤ Subgroup.centralizer (B.S)` (equivalently: `B₀` centralizes the whole
  Sylow 2-subgroup `S = ⟨S₀, s⟩`). -/
theorem Case2PrePlusOfCentralizer :
    ∀ (G : Type) [Group G] [Finite G] (I : Work.GW2.C4Inputs), Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        h.D.B0 ≤ Subgroup.centralizer ((B.S : Subgroup G) : Set G) →
        h.D.B0 = (B.U ⊓ h.D.M) ⊓
          Subgroup.centralizer ((((B.S : Subgroup G) ⊓ Work.GW2.layerIn h.D.M : Subgroup G)) : Set G) := by
  intro G _ _ I _ B h hB0
  -- §4 (9): `S ≤ E(M)`, so `S ⊓ E(M) = S`.
  obtain ⟨p, k, hp, _hodd, _hq, _hiso, hSle⟩ := h.nine
  have hinf : (B.S : Subgroup G) ⊓ Work.GW2.layerIn h.D.M = (B.S : Subgroup G) :=
    inf_eq_left.mpr hSle
  rw [hinf]
  -- `s ∈ S` by `D.s_mem`, so `C_G(S) ≤ C_G({s})`.
  have hs : h.D.s ∈ (B.S : Subgroup G) := (Subgroup.mem_inf.mp h.D.s_mem).1
  have hcen : Subgroup.centralizer ((B.S : Subgroup G) : Set G) ≤
      Subgroup.centralizer ({h.D.s} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hs)
  -- `B₀ ≤ C_G(S)` transports to `(U ⊓ M) ⊓ C_G({s}) ≤ C_G(S)` via `D.B0_def`.
  have hB0' : (B.U ⊓ h.D.M) ⊓ Subgroup.centralizer ({h.D.s} : Set G) ≤
      Subgroup.centralizer ((B.S : Subgroup G) : Set G) := by
    rw [← h.D.B0_def]; exact hB0
  refine Eq.symm ?_
  rw [h.D.B0_def]
  -- goal : `(U ⊓ M) ⊓ C_G(S) = (U ⊓ M) ⊓ C_G({s})`
  exact le_antisymm (le_inf inf_le_left (le_trans inf_le_right hcen))
    (le_inf inf_le_left hB0')

end Work.CORE4
