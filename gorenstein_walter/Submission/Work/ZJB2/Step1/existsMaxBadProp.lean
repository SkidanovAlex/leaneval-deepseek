import Mathlib
import Submission.Work.ZJB.Step1.Defs

/-!
# ZJB — step (I).0: a violation of (I) gives a `MaxBad` Sylow subgroup

Glauberman 1968, p. 1118 (the paper's step (I), first line): if `S` is a Sylow `p`-subgroup and
`Z(S)^g ≤ S` but `Z(S)^g ⊄ Z(J(S))`, then `S₁ := S^{g⁻¹} = g S g⁻¹` is a *bad* Sylow subgroup
(`Z(S) ≤ S₁` but `Z(S) ⊄ Z(J(S₁))`), and among the finitely many bad Sylow subgroups one may
choose one maximising `|D| = |N(J(S)) ∩ S₁|`.  That maximiser is `MaxBad S S₁`.

The choice of `S₁` is the paper's: conjugating `Z(S)^g ≤ S` by `g⁻¹` gives
`Z(S) = (Z(S)^g)^{g⁻¹} ≤ S^{g⁻¹}`, while `Z(J(S₁)) = Z(J(S))^{g⁻¹}` turns the failure
`Z(S)^g ⊄ Z(J(S))` into the failure `Z(S) ⊄ Z(J(S₁))`; the two are exchanged by `ZJ_map_conj`.

The maximality is an argmax of `Nat.card (Dsub S ·)` over the finite (nonempty) set of bad Sylow
subgroups; `Finite (Sylow p G)` holds because `G` is finite.
-/

namespace Work.ZJB2.Step1

open Work.GW2 Work.ZJB Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Conjugation covariance of `Z(J(-))` in the pointwise-smul form used below. -/
theorem ZJ_pointwise_smul_conj (P : Subgroup G) (g : G) :
    ZJ (MulAut.conj g • P) = (ZJ P).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.pointwise_smul_def]
  exact Work.ZJB.ZJ_map_conj P g

/-- `S₁` is *bad* for `S` (`S₁` a Sylow `p`-subgroup): `Z(S) ≤ S₁` but `Z(S) ⊄ Z(J(S₁))`. -/
def BadSylow (S S₁ : Sylow p G) : Prop :=
  ZS (S : Subgroup G) ≤ (S₁ : Subgroup G) ∧ ¬ ZS (S : Subgroup G) ≤ ZJ (S₁ : Subgroup G)

theorem existsMaxBadProp {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] : Work.ZJB.ExistsMaxBadProp p G := by
  classical
  intro S g h1 h2
  -- `S₁ := g • S = S^{g⁻¹}` is bad.
  have ha : ZS (S : Subgroup G) ≤ ((g • S : Sylow p G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    intro x hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hxg : (MulAut.conj g)⁻¹ • x = g⁻¹ * x * g := by
      rw [MulAut.smul_def, MulAut.inv_apply, MulAut.conj_symm_apply]
    rw [hxg]
    have : g⁻¹ * x * g ∈ pconj (ZS (S : Subgroup G)) g := by
      rw [Work.ZJB.mem_pconj]
      convert hx using 1
      group
    exact h1 this
  have hb : ¬ ZS (S : Subgroup G) ≤ ZJ ((g • S : Sylow p G) : Subgroup G) := by
    intro hgood
    apply h2
    rw [Sylow.coe_subgroup_smul] at hgood
    rw [ZJ_pointwise_smul_conj (S : Subgroup G) g] at hgood
    intro x hx
    rw [Work.ZJB.mem_pconj] at hx
    have hy' : g * x * g⁻¹ ∈ (ZJ (S : Subgroup G)).map (MulAut.conj g).toMonoidHom := hgood hx
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy'
    have key : x = z := by
      have hgcd : (MulEquiv.toMonoidHom (MulAut.conj g)) z = g * z * g⁻¹ := by
        simp [MulAut.conj_apply]
      have h2' : g * x * g⁻¹ = g * z * g⁻¹ := by rw [← hzy, hgcd]
      exact mul_left_cancel (mul_right_cancel h2')
    rw [key]
    exact hz
  have hbad_g : BadSylow S (g • S) := ⟨ha, hb⟩
  letI : Fintype (Sylow p G) := Fintype.ofFinite (Sylow p G)
  obtain ⟨S₁, hS₁mem, hS₁max⟩ := Finset.exists_max_image
    (Finset.univ.filter (BadSylow S)) (fun S₂ : Sylow p G => Nat.card (Dsub S S₂))
    ⟨g • S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad_g⟩⟩
  have hbad₁ : BadSylow S S₁ := (Finset.mem_filter.mp hS₁mem).2
  refine ⟨S₁, hbad₁.1, hbad₁.2, ?_⟩
  intro S₂ hZS hlt
  by_contra hcon
  have hmem : S₂ ∈ Finset.univ.filter (BadSylow S) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hZS, hcon⟩
  exact not_lt_of_ge (hS₁max S₂ hmem) hlt

end Work.ZJB2.Step1
