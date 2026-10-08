/-
# `Work.NormalComplement.Sec5Fix.Defs`

Vocabulary for the `Sec5Fix` development of Peterfalvi I Ch. III §5 Prop. 2 (a)
(`orderOf (u * t) ∈ {3, 5}`).

With `H` strongly embedded, `t ∉ H` an involution, `D = H ⊓ H^t = twoPoint H t`,
`V = C_D(t) = centD H t` and `F = O^{2'}(C_G(V)) = p3F V`, the proof of Prop. 2 (a) applies
Appendix III to the action of `F` on the set `Ω_V = fixedPts H V` of fixed points of `V` (modulo
the kernel of that action).  This file provides the objects:

* `Vc H t`, `Fc H t`, `Om H t` — the abbreviations `V`, `F`, `Ω_V`;
* `Zact H t` — the kernel of the action of `F` on `Ω_V`, as a subgroup of the ambient group;
* the induced action of `↥(Fc H t)` on `↥(Om H t)`;
* the basic API for `Zact` (`mem_Zact`, `Zact_le`, `Zact_fixes`, `Fc_le_normalizer_Zact`, ...).

Everything here is `sorry`-free, so the child lemmas of the development may import it.
-/
import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.P3Sub.Helpers
import Submission.Work.ThreePoints.Basic
import Submission.Work.ThreePoints.Omega

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 400000

open Classical
open Submission.Blueprint
open LeanEval.GroupTheory.Defs

namespace Work.NormalComplement.Sec5Fix

variable {G : Type} [Group G] [Finite G]

/-- `V = centD H t = C_D(t)` with `D = twoPoint H t`. -/
abbrev Vc (H : Subgroup G) (t : G) : Subgroup G := Submission.Blueprint.centD H t

/-- `F = O^{2'}(C_G(V)) = p3F V`. -/
noncomputable abbrev Fc (H : Subgroup G) (t : G) : Subgroup G :=
  Work.ThreePoints.p3F (Submission.Blueprint.centD H t)

/-- `Ω_V`, the set of fixed points of `V` on `G ⧸ H`. -/
abbrev Om (H : Subgroup G) (t : G) : Set (G ⧸ H) :=
  Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t)

/-- `V ≤ H`. -/
theorem Vc_le_H (H : Subgroup G) (t : G) : Vc H t ≤ H :=
  le_trans inf_le_left inf_le_left

/-- `V ≤ D = twoPoint H t`. -/
theorem Vc_le_twoPoint (H : Subgroup G) (t : G) : Vc H t ≤ twoPoint H t := inf_le_left

/-- `V ≤ C_G(t)`. -/
theorem Vc_le_centralizer (H : Subgroup G) (t : G) :
    Vc H t ≤ Subgroup.centralizer ({t} : Set G) := inf_le_right

/-- `F` normalises `V`. -/
theorem Fc_le_normalizer (H : Subgroup G) (t : G) :
    Fc H t ≤ Subgroup.normalizer (Vc H t : Set G) :=
  Work.ThreePoints.p3F_le_normalizer _

/-- `Ω_V` is invariant under `F`. -/
theorem smul_mem_Om {H : Subgroup G} {t : G} {g : G} (hg : g ∈ Fc H t) {ω : G ⧸ H}
    (hω : ω ∈ Om H t) : g • ω ∈ Om H t := by
  rw [Work.ThreePoints.mem_fixedPts] at hω ⊢
  intro v hv
  have hconj : g⁻¹ * v * g ∈ Vc H t :=
    ((Subgroup.mem_normalizer_iff''.mp (Fc_le_normalizer H t hg)) v).mp hv
  calc v • (g • ω) = (v * g) • ω := (mul_smul v g ω).symm
    _ = (g * (g⁻¹ * v * g)) • ω := by rw [show v * g = g * (g⁻¹ * v * g) from by group]
    _ = g • ((g⁻¹ * v * g) • ω) := mul_smul g _ ω
    _ = g • ω := by rw [hω _ hconj]

/-- `F ≤ C_G(V)`. -/
theorem Fc_le_centralizer (H : Subgroup G) (t : G) :
    Fc H t ≤ Subgroup.centralizer (Vc H t : Set G) :=
  Work.ThreePoints.p3F_le_centralizer _

/-- The action of `F` on `Ω_V`, transported to the subtype `↥(Om H t)`. -/
noncomputable instance instMulActionOmega {H : Subgroup G} {t : G} :
    MulAction ↥(Fc H t) ↥(Om H t) where
  smul g ω := ⟨(g : G) • (ω : G ⧸ H), smul_mem_Om g.2 ω.2⟩
  one_smul ω := by
    apply Subtype.ext
    change (1 : G) • (ω : G ⧸ H) = (ω : G ⧸ H)
    rw [one_smul]
  mul_smul g h ω := by
    apply Subtype.ext
    change ((g : G) * (h : G)) • (ω : G ⧸ H) = (g : G) • ((h : G) • (ω : G ⧸ H))
    rw [mul_smul]

@[simp] theorem smul_coe {H : Subgroup G} {t : G} (g : ↥(Fc H t)) (ω : ↥(Om H t)) :
    ((g • ω : ↥(Om H t)) : G ⧸ H) = (g : G) • (ω : G ⧸ H) := rfl

/-- The kernel of the action of `F = O^{2'}(C_G(V))` on `Ω_V = fixedPts H V`, as a subgroup of the
ambient group `G`.  By construction its elements are exactly the elements of `F` acting trivially
on `Ω_V`. -/
noncomputable def Zact (H : Subgroup G) (t : G) : Subgroup G where
  carrier := {x : G | x ∈ Fc H t ∧ ∀ ω : G ⧸ H, ω ∈ Om H t → x • ω = ω}
  mul_mem' := by
    rintro x y ⟨hxF, hx⟩ ⟨hyF, hy⟩
    refine ⟨(Fc H t).mul_mem hxF hyF, ?_⟩
    intro ω hω
    rw [mul_smul, hy ω hω, hx ω hω]
  one_mem' := ⟨(Fc H t).one_mem, fun ω _ => one_smul G ω⟩
  inv_mem' := by
    rintro x ⟨hxF, hx⟩
    refine ⟨(Fc H t).inv_mem hxF, ?_⟩
    intro ω hω
    have hmem : x⁻¹ • ω ∈ Om H t := smul_mem_Om ((Fc H t).inv_mem hxF) hω
    have h1 : x • (x⁻¹ • ω) = x⁻¹ • ω := hx _ hmem
    rw [smul_inv_smul] at h1
    exact h1.symm

theorem mem_Zact {H : Subgroup G} {t : G} {x : G} :
    x ∈ Zact H t ↔ x ∈ Fc H t ∧ ∀ ω : G ⧸ H, ω ∈ Om H t → x • ω = ω := Iff.rfl

theorem Zact_le (H : Subgroup G) (t : G) : Zact H t ≤ Fc H t :=
  fun _ hx => (mem_Zact.mp hx).1

theorem Zact_fixes {H : Subgroup G} {t : G} {x : G} (hx : x ∈ Zact H t) {ω : G ⧸ H}
    (hω : ω ∈ Om H t) : x • ω = ω :=
  (mem_Zact.mp hx).2 ω hω

/-- Elements of `Zact` fix `H` (i.e. lie in `H`). -/
theorem Zact_le_H (H : Subgroup G) (t : G) : Zact H t ≤ H := by
  intro x hx
  have h := Zact_fixes hx (Work.ThreePoints.pt_mem_fixedPts_of_le_centD (le_refl (Vc H t)))
  have h' : (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk (1 : G) := by
    simpa using h
  have h2 : x⁻¹ ∈ H := by simpa using (QuotientGroup.eq.mp h')
  simpa using H.inv_mem h2

/-- Conjugation by an element of `F` preserves `Zact`. -/
theorem conj_mem_Zact {H : Subgroup G} {t : G} {f : G} (hf : f ∈ Fc H t) {z : G}
    (hz : z ∈ Zact H t) : f * z * f⁻¹ ∈ Zact H t := by
  have hf' : f⁻¹ ∈ Fc H t := (Fc H t).inv_mem hf
  refine mem_Zact.mpr ⟨(Fc H t).mul_mem ((Fc H t).mul_mem hf (Zact_le H t hz)) hf', ?_⟩
  intro ω hω
  rw [mul_smul, mul_smul, Zact_fixes hz (smul_mem_Om hf' hω), smul_inv_smul]

/-- The kernel of the action of `F` on `Ω_V` is normal in `F`. -/
theorem Fc_le_normalizer_Zact (H : Subgroup G) (t : G) :
    Fc H t ≤ Subgroup.normalizer (Zact H t : Set G) := by
  intro f hf
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact conj_mem_Zact hf
  · intro hz
    have hf' : f⁻¹ ∈ Fc H t := (Fc H t).inv_mem hf
    have h := conj_mem_Zact (H := H) (t := t) hf' hz
    convert h using 1
    group

/-- `Zact` acts trivially on `Ω_V`. -/
theorem Zact_le_stabilizer {H : Subgroup G} {t : G} {ω : G ⧸ H} (hω : ω ∈ Om H t) :
    Zact H t ≤ MulAction.stabilizer G ω :=
  fun _ hx => MulAction.mem_stabilizer_iff.mpr (Zact_fixes hx hω)

/-- `Zact ≤ twoPoint H t = D`. -/
theorem Zact_le_twoPoint (H : Subgroup G) (t : G) : Zact H t ≤ twoPoint H t := by
  intro x hx
  refine Subgroup.mem_inf.mpr ⟨Zact_le_H H t hx, ?_⟩
  -- `x` fixes the point `tH = H^t`, hence lies in `H^t = conj t H`
  have hω : (QuotientGroup.mk t : G ⧸ H) ∈ Om H t :=
    Work.ThreePoints.mk_t_mem_fixedPts_of_le_centD (le_refl (Vc H t))
  have h := Zact_fixes hx hω
  have h' : (QuotientGroup.mk (x * t) : G ⧸ H) = QuotientGroup.mk t := by
    simpa using h
  have h2 : (x * t)⁻¹ * t ∈ H := QuotientGroup.eq.mp h'
  have h3 : t⁻¹ * x⁻¹ * t ∈ H := by
    simpa [mul_assoc] using h2
  -- `t⁻¹ * x⁻¹ * t ∈ H` says `x⁻¹ ∈ conj t H`
  have h4 : x⁻¹ ∈ conj t H := by
    rw [Submission.Blueprint.conj, Subgroup.mem_map]
    refine ⟨t⁻¹ * x⁻¹ * t, h3, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  simpa using (conj t H).inv_mem h4

end Work.NormalComplement.Sec5Fix
