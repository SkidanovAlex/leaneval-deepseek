import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Prove.Step9Defs
import Submission.Work.ThmF.ChV3.Prove.S4_centD_not_stronglyReal
import Submission.Work.ThmF.ChV3.Prove.OrbitCountDefs
import Submission.Work.ThmF.ChV3.Prove.card_normalizer_eq_orbit_mul_centralizer
import Submission.Work.ThmF.ChV3.Prove.orb_eq_AT_union_101
import Submission.Work.ThmF.ChV3.Prove.AT_ncard_eq_101

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.orbit_count_101`

The orbit count of Peterfalvi II Ch. V §3, step (12), case (10-1): the number of conjugates of
`P` under `N_G(R)` is `|P|^m`, whence

`|N_G(R)| = |P|^m · |C_G(P)|`.

## The argument

Let `S = N_G(R)`, `C = C_G(P)`, `K = C_Q(P)`, and let `𝒜 = AT R T P` be the set of subgroups
`A ≤ R` with `Nat.card A = Nat.card P`, `A ⊄ T`, `A ≠ P`.

* `orb_eq_AT_union_101` : the `S`-orbit of `P` is `𝒜 ∪ {P}`.
* `AT_ncard_eq_101` : if `𝒜 ≠ ∅` then `|𝒜| = |K|` (the map `y ↦ y A₀ y⁻¹` is a bijection
  `K → 𝒜`, from the sharp transitivity `Step11Out.reg`).
* `𝒜 ≠ ∅` because otherwise the orbit would be `{P}`, i.e. `S ≤ N_G(P) = C ≤ S`, contradicting
  `hNGne`.

Hence `|orb P S| = |𝒜| + 1 = |K| + 1 = orderOf (s*t)^m = |P|^m` (`hcq`, `hpf`), and the
orbit–stabilizer identity `card_normalizer_eq_orbit_mul_centralizer` gives `|S| = |orb| · |C|`.
-/

open scoped Pointwise

namespace Work.ThmF.ChV3.Prove

open Work.ThmF.ChV3

theorem orbit_count_101 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    {R T : Subgroup G} {m : ℕ}
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (hpf : Nat.card P = orderOf (s * t)) (hm : 1 ≤ m)
    (hRc : R ≤ Work.ThmF.ChV3.CG P) (hRn : Work.ThmF.ChV3.CG P ≤ Work.ThmF.ChV3.NG R)
    (hKer : Work.ThmF.ChV3.Ker H Q P t = P)
    (hcardR : Nat.card R = Nat.card ↥(Work.ThmF.ChV3.Ker H Q P t) * orderOf (s * t) ^ m)
    (hcq : Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = orderOf (s * t) ^ m)
    (hNG : Work.ThmF.ChV3.NG P = Work.ThmF.ChV3.CG P)
    (h11 : Work.ThmF.ChV3.Step11Out H Q t P R T)
    (hsT : ∀ x ∈ T, s * x * s⁻¹ = x⁻¹)
    (hNGne : Work.ThmF.ChV3.NG R ≠ Work.ThmF.ChV3.NG P) :
    Nat.card ↥(Work.ThmF.ChV3.NG R) = Nat.card P ^ m * Nat.card ↥(Work.ThmF.ChV3.CG P) := by
  classical
  -- The orbit of `P` under `N_G(R)` is not `{P}`, else `N_G(R) ≤ N_G(P) = C_G(P) ≤ N_G(R)`.
  have hne : orb P (NG R) ≠ {P} := by
    intro h
    have hle : NG R ≤ NG P := by
      intro g hg
      rw [← cj_eq_self_iff]
      have hmem : cj g P ∈ orb P (NG R) := ⟨g, hg, rfl⟩
      rw [h] at hmem
      simpa using hmem
    have hle' : NG R ≤ CG P := hle.trans (le_of_eq hNG)
    have hEq : NG R = CG P := le_antisymm hle' hRn
    exact hNGne (hEq.trans hNG.symm)
  -- The set-theoretic half: `orb P (NG R) = AT R T P ∪ {P}`.
  have h2 : orb P (NG R) = AT R T P ∪ {P} := orb_eq_AT_union_101 hC4 c hRn hNG h11 hsT hNGne
  -- `AT R T P` is nonempty because the orbit is not `{P}`.
  have hATne : (AT R T P).Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    exact hne (by rw [h2, hc, Set.empty_union])
  -- The counting half: `|AT R T P| = |C_Q(P)|`.
  have hAT : (AT R T P).ncard = Nat.card ↥(CQ Q P) := AT_ncard_eq_101 hRn h11 hATne
  -- Hence the orbit has `|C_Q(P)| + 1 = orderOf (s*t)^m = |P|^m` elements.
  have hOrb : (orb P (NG R)).ncard = Nat.card P ^ m := by
    have hdisj : Disjoint (AT R T P) ({P} : Set (Subgroup G)) := by
      rw [Set.disjoint_left]
      intro A hA hAP
      rw [Set.mem_singleton_iff] at hAP
      exact hA.2.2.2 hAP
    rw [h2, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), hAT, Set.ncard_singleton]
    rw [hcq, ← hpf]
  -- Orbit–stabilizer for the conjugation action of `N_G(R)` on `Subgroup G`.
  have h1 : Nat.card ↥(NG R) = (orb P (NG R)).ncard * Nat.card ↥(CG P) :=
    card_normalizer_eq_orbit_mul_centralizer hRn hNG
  rw [h1, hOrb]

end Work.ThmF.ChV3.Prove
