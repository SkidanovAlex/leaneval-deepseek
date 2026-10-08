import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.ChV12.lemma2b

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV3.Prove

/-- `C_G(P)` acts on `Ω = G ⧸ H` and, by `ChV12.centralizer_transitive_fixedPts` (Peterfalvi II
Ch. V §2 Lemma 2 (a)'s transitivity, applied to `P ≤ V = C_D(t)`), it is transitive on the fixed
points `Ω_P = fixedPts H P`; the point stabiliser of the base point `H` is `C_G(P) ⊓ H`.  The
orbit–stabiliser theorem then gives the counting identity `|C_G(P)| = |Ω_P| |C_G(P) ⊓ H|`. -/
theorem S1_CG_card_orbit {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) :
    Nat.card ↥(Work.ThmF.ChV3.CG P) =
      (Submission.Blueprint.fixedPts H P).ncard * Nat.card ↥(H ⊓ Work.ThmF.ChV3.CG P) := by
  classical
  have hPleH : P ≤ H := fun x hx => (Work.ThreePoints.mem_centD.mp (c.P_le hx)).1
  -- the base point `H` of `Ω` is fixed by `P`
  have hbase : ((1 : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H P := by
    rw [Work.ThreePoints.mem_fixedPts]
    intro x hx
    rw [Work.ThreePoints.smul_mk]
    exact QuotientGroup.eq.mpr (by simpa using hPleH hx)
  -- `C_G(P)` preserves the fixed points of `P`
  have hpres : ∀ (l : ↥(Work.ThmF.ChV3.CG P)) (ω : G ⧸ H),
      ω ∈ Submission.Blueprint.fixedPts H P → l • ω ∈ Submission.Blueprint.fixedPts H P := by
    intro l ω hω
    rw [Work.ThreePoints.mem_fixedPts] at hω ⊢
    intro x hx
    have hl : x * (l : G) = (l : G) * x := Subgroup.mem_centralizer_iff.mp l.2 x hx
    calc x • (l • ω) = (x * (l : G)) • ω := by
          rw [Subgroup.smul_def]; exact (mul_smul x (l : G) ω).symm
      _ = ((l : G) * x) • ω := by rw [hl]
      _ = (l : G) • (x • ω) := mul_smul (l : G) x ω
      _ = (l : G) • ω := by rw [hω x hx]
      _ = l • ω := (Subgroup.smul_def l ω).symm
  -- `Ω_P` is exactly the orbit of the base point under `C_G(P)`
  have horbit : Submission.Blueprint.fixedPts H P =
      MulAction.orbit ↥(Work.ThmF.ChV3.CG P) ((1 : G) : G ⧸ H) := by
    ext ω
    constructor
    · intro hω
      obtain ⟨l, hl⟩ := Work.ThmF.ChV12.centralizer_transitive_fixedPts c.split c.P_le ω hω
      exact MulAction.mem_orbit_iff.mpr ⟨l, by rw [Subgroup.smul_def]; exact hl⟩
    · intro hω
      obtain ⟨l, hl⟩ := MulAction.mem_orbit_iff.mp hω
      rw [← hl]
      exact hpres l _ hbase
  -- the point stabiliser of the base point in `C_G(P)` is `C_G(P) ⊓ H`
  have hstab : MulAction.stabilizer ↥(Work.ThmF.ChV3.CG P) ((1 : G) : G ⧸ H) =
      (H ⊓ Work.ThmF.ChV3.CG P).subgroupOf (Work.ThmF.ChV3.CG P) := by
    ext x
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      refine ⟨?_, x.2⟩
      have h : ((x : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
        simpa [Subgroup.smul_def, Work.ThreePoints.smul_mk] using hx
      have h' := QuotientGroup.eq.mp (by simpa using h)
      simpa using h'
    · intro hx
      have h : ((x : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
        rw [QuotientGroup.eq]; simpa using hx.1
      simpa [Subgroup.smul_def, Work.ThreePoints.smul_mk] using h
  have hcard_stab : Nat.card ↥(MulAction.stabilizer ↥(Work.ThmF.ChV3.CG P) ((1 : G) : G ⧸ H))
      = Nat.card ↥(H ⊓ Work.ThmF.ChV3.CG P) := by
    have h1 : Nat.card ↥(MulAction.stabilizer ↥(Work.ThmF.ChV3.CG P) ((1 : G) : G ⧸ H))
        = Nat.card ↥((H ⊓ Work.ThmF.ChV3.CG P).subgroupOf (Work.ThmF.ChV3.CG P)) :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun x => by rw [hstab]))
    have h2 : Nat.card ↥((H ⊓ Work.ThmF.ChV3.CG P).subgroupOf (Work.ThmF.ChV3.CG P))
        = Nat.card ↥(H ⊓ Work.ThmF.ChV3.CG P) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show H ⊓ Work.ThmF.ChV3.CG P ≤ Work.ThmF.ChV3.CG P from inf_le_right)).toEquiv
    rw [h1, h2]
  have horbit_card : Nat.card ↥(MulAction.orbit ↥(Work.ThmF.ChV3.CG P) ((1 : G) : G ⧸ H))
      = (Submission.Blueprint.fixedPts H P).ncard := by
    rw [← horbit]
    exact Nat.card_coe_set_eq _
  -- orbit–stabiliser
  have hprincipal : Nat.card ↥(Work.ThmF.ChV3.CG P) =
      Nat.card ↥(MulAction.orbit ↥(Work.ThmF.ChV3.CG P) ((1 : G) : G ⧸ H)) *
        Nat.card ↥(MulAction.stabilizer ↥(Work.ThmF.ChV3.CG P) ((1 : G) : G ⧸ H)) := by
    rw [← Nat.card_prod]
    exact (Nat.card_congr
      (MulAction.orbitProdStabilizerEquivGroup ↥(Work.ThmF.ChV3.CG P) ((1 : G) : G ⧸ H))).symm
  rw [hprincipal, horbit_card, hcard_stab]

end Work.ThmF.ChV3.Prove
