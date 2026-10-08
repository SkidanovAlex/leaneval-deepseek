import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.PGroup

/-- **FT Lemma 8.2 (ii)** (the "p'-automorphisms of a `p`-group act faithfully on a critical
subgroup" part).  If `C` is a critical subgroup of the `p`-group `P`, then every element `g`
which normalizes `P`, centralizes `C`, and has order prime to `p` centralizes `P` as well.

Equivalently: the conjugation action of `⟨g⟩` on `P` is a `p'`-automorphism of `P` which is
faithful on the critical subgroup `C`.

The proof is the classical one: by the Three Subgroups Lemma the commutator `⁅P, ⟨g⟩⁆` lies in
`P ⊓ C_P(C) ≤ C` (using `[P,C] ≤ Z(C)` and `[⟨g⟩, C] = 1`).  Hence for `x ∈ P` the commutator
`c = ⁅x, g⁆` is an element of the `p`-group `C` which is fixed by `g`; the identity
`⁅x, g^n⁆ = ⁅x, g⁆^n` (valid because `g` centralizes `c`) with `n = orderOf g` gives `c^n = 1`,
and since `orderOf c` is a power of `p` while `n` is coprime to `p`, we get `c = 1`. -/
theorem centralizes_of_isCriticalSubgroup {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (P C : Subgroup G) [Finite P] (hP : IsPGroup p P) (hC : Work.PGroup.IsCriticalSubgroup p P C)
    {g : G} (hgN : g ∈ Subgroup.normalizer (P : Set G))
    (hgc : g ∈ Subgroup.centralizer (C : Set G)) (hg' : (orderOf g).Coprime p) :
    g ∈ Subgroup.centralizer (P : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hAleN : Subgroup.zpowers g ≤ Subgroup.normalizer (P : Set G) := Subgroup.zpowers_le.mpr hgN
  have hAleC : Subgroup.zpowers g ≤ Subgroup.centralizer (C : Set G) :=
    Subgroup.zpowers_le.mpr hgc
  -- The Three Subgroups Lemma shows that `⁅P, ⟨g⟩⁆` commutes with `C`.
  have hPA_le_cent : ⁅P, Subgroup.zpowers g⁆ ≤ Subgroup.centralizer (C : Set G) := by
    have h1 : ⁅⁅Subgroup.zpowers g, C⁆, P⁆ = ⊥ := by
      have hz : ⁅Subgroup.zpowers g, C⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hAleC
      rw [hz, Subgroup.commutator_bot_left]
    have h2 : ⁅⁅C, P⁆, Subgroup.zpowers g⁆ = ⊥ := by
      have hle : ⁅C, P⁆ ≤ Work.PGroup.centerIn C := by
        rw [Subgroup.commutator_comm]
        exact hC.commutator_le_center
      have hcenter : ⁅Work.PGroup.centerIn C, Subgroup.zpowers g⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact (Subgroup.mem_centralizer_iff.mp (hAleC ha) z (Work.PGroup.centerIn_le C hz)).symm
      exact le_bot_iff.mp ((Subgroup.commutator_mono hle le_rfl).trans (le_of_eq hcenter))
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2)
  have hPA_le_P : ⁅P, Subgroup.zpowers g⁆ ≤ P :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hAleN
  -- Hence `⁅P, ⟨g⟩⁆ ≤ P ⊓ C_P(C) ≤ C` by self-centralization.
  have hPA_le_C : ⁅P, Subgroup.zpowers g⁆ ≤ C :=
    le_trans (le_inf hPA_le_P hPA_le_cent) hC.self_centralizing
  have hg_mem_A : g ∈ Subgroup.zpowers g := Subgroup.mem_zpowers g
  have hmem := Subgroup.commutator_mem_commutator hx hg_mem_A
  have hcC : ⁅x, g⁆ ∈ C := hPA_le_C hmem
  have hcP : ⁅x, g⁆ ∈ P := hPA_le_P hmem
  have hcomm : Commute g ⁅x, g⁆ := by
    show g * ⁅x, g⁆ = ⁅x, g⁆ * g
    exact (Subgroup.mem_centralizer_iff.mp hgc ⁅x, g⁆ hcC).symm
  -- `⁅x, g⁆ ^ orderOf g = ⁅x, g ^ orderOf g⁆ = 1`.
  have hpow : ⁅x, g⁆ ^ orderOf g = 1 := by
    rw [hcomm.commutatorElement_pow_right (orderOf g), pow_orderOf_eq_one,
      commutatorElement_one_right]
  have hdvdc : orderOf ⁅x, g⁆ ∣ orderOf g := orderOf_dvd_iff_pow_eq_one.mpr hpow
  -- `orderOf ⁅x, g⁆` also divides a power of `p`, since `⁅x, g⁆ ∈ C ≤ P`.
  obtain ⟨k, hk⟩ := hP (⟨⁅x, g⁆, hcP⟩ : P)
  have hdvdp : orderOf ⁅x, g⁆ ∣ p ^ k := by
    rw [← Subgroup.orderOf_mk ⁅x, g⁆ hcP]
    exact orderOf_dvd_iff_pow_eq_one.mpr hk
  have hcop : Nat.Coprime (orderOf g) (p ^ k) := Nat.Coprime.pow_right k hg'
  exact commutatorElement_eq_one_iff_mul_comm.mp
    (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvdc hdvdp))

end Work.PGroup
