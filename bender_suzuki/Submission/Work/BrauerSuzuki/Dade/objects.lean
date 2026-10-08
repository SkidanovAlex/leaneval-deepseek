import Mathlib
import Submission.Work.BrauerSuzuki.Dade.defs
import Submission.Work.BrauerSuzuki.Dade.complement_and_sqrtSet
import Submission.Work.BrauerSuzuki.Dade.complement_hom
import Submission.Work.BrauerSuzuki.Quaternion.characters
import Submission.Work.CharCore.Defs
import Submission.Work.CharCore.Basic
import Submission.Work.Induction.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.BrauerSuzuki.Dade

open Classical
open scoped Pointwise

variable {G : Type*} [Group G] [Fintype G]

/-!
# The objects of Dade's Theorem 6.8

With `S` a Sylow `2`-subgroup of a finite group `G`, `d : GenQuaternionData ↥S` with `3 ≤ d.n`,
`σ = τ ^ 2`, `ι = τ ^ (2 ^ (n-1))` and `H = N_G (⟨σ⟩)`:

* `Ksub S d hn` is the normal `2`-complement `K ⊴ H` of Dade's Lemma 6.9;
* `phi S d hn : ↥H →* ↥S` is the projection `H → H/K ≅ S` of Lemma 6.10;
* `lam`, `th : ↥S → ℂ` are Dade's two characters of the quaternion group (6.3)–(6.6);
* `alpha S d hn : ↥H → ℂ` is `(1 + lam - th) ∘ φ`, the virtual character of `H` of Theorem 6.8.
-/

/-- Dade's normal `2`-complement `K ⊴ N_G(⟨σ⟩)`, whose existence is Lemma 6.9. -/
noncomputable def Ksub (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) : Subgroup G := Classical.choose (complement_and_sqrtSet S d hn)

/-- `Ksub S d hn` is contained in `C_G(σ)`, hence in its normalizer. -/
theorem Ksub_le_hsub (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) : Ksub S d hn ≤ Hsub S d := by
  have h := (Classical.choose_spec (complement_and_sqrtSet S d hn)).2.2.2.2.2.2
  rw [show Hsub S d = Ksub S d hn ⊔ (S : Subgroup G) from
    ((Classical.choose_spec (complement_and_sqrtSet S d hn)).2.2.2.1).symm]
  exact le_sup_left

/-- The Sylow `2`-subgroup `S` lies in `H = N_G(⟨σ⟩)`. -/
theorem sylow_le_Hsub (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    (S : Subgroup G) ≤ Hsub S d := sylow_le_normalizer S d

theorem Ksub_inf_sylow (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) : Ksub S d hn ⊓ (S : Subgroup G) = ⊥ :=
  (Classical.choose_spec (complement_and_sqrtSet S d hn)).2.2.1

theorem Ksub_sup_hsub (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) : Ksub S d hn ⊔ (S : Subgroup G) = Hsub S d :=
  (Classical.choose_spec (complement_and_sqrtSet S d hn)).2.2.2.1

theorem Ksub_odd (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) : Odd (Nat.card (Ksub S d hn)) :=
  (Classical.choose_spec (complement_and_sqrtSet S d hn)).2.2.2.2.1

theorem Ksub_centralizes (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) :
    ∀ x ∈ Ksub S d hn, x * sigma S d = sigma S d * x :=
  (Classical.choose_spec (complement_and_sqrtSet S d hn)).2.2.2.2.2.1

/-- Dade's Lemma 6.10: `√σ = ⟨τ⟩ K \ ⟨τ⁴⟩ K`. -/
theorem sqrtSet_eq_prod (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) :
    Work.BrauerSuzuki.sqrtSet (sigma S d) =
      ((Subgroup.zpowers ((d.tau : ↥S) : G) : Set G) * (Ksub S d hn : Set G)) \
        ((Subgroup.zpowers (((d.tau : ↥S) : G) ^ 4) : Set G) * (Ksub S d hn : Set G)) :=
  (Classical.choose_spec (complement_and_sqrtSet S d hn)).2.2.2.2.2.2

theorem Ksub_conj_mem (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) : ∀ k ∈ Ksub S d hn, ∀ h ∈ Hsub S d, h * k * h⁻¹ ∈ Ksub S d hn :=
  fun k hk h hh =>
    (Subgroup.mem_normalizer_iff.mp
      ((Classical.choose_spec (complement_and_sqrtSet S d hn)).2.1 hh) k).mp hk

/-- The projection `φ : ↥H →* ↥S` with kernel `K` (Dade's Lemma 6.10). -/
noncomputable def phi (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) : ↥(Hsub S d) →* ↥S :=
  Classical.choose (complement_hom (S : Subgroup G) (Ksub S d hn) (Hsub S d)
    (Ksub_le_hsub S d hn) (sylow_le_Hsub S d)
    (Ksub_inf_sylow S d hn) (Ksub_sup_hsub S d hn) (Ksub_conj_mem S d hn))

theorem phi_spec (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) :
    (∀ s : ↥S, phi S d hn ⟨(s : G), sylow_le_Hsub S d s.2⟩ = s) ∧
    (∀ h : ↥(Hsub S d), phi S d hn h = 1 ↔ ((h : G) ∈ Ksub S d hn)) ∧
    Function.Surjective (phi S d hn) ∧
    (∀ h : ↥(Hsub S d), ∃ k ∈ Ksub S d hn, (h : G) = ((phi S d hn h : ↥S) : G) * k) :=
  Classical.choose_spec (complement_hom (S : Subgroup G) (Ksub S d hn) (Hsub S d)
    (Ksub_le_hsub S d hn) (sylow_le_Hsub S d)
    (Ksub_inf_sylow S d hn) (Ksub_sup_hsub S d hn) (Ksub_conj_mem S d hn))

/-- The non-trivial linear character `λ` of the generalized quaternion group `↥S`. -/
noncomputable def lam (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    ↥S → ℂ :=
  Classical.choose (Work.BrauerSuzuki.Quaternion.characters d)

/-- The degree-`2` irreducible character `θ = μ^S` of `↥S`. -/
noncomputable def th (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    ↥S → ℂ :=
  Classical.choose (Classical.choose_spec (Work.BrauerSuzuki.Quaternion.characters d))

theorem lam_mem_Irr (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    lam S d ∈ Work.CharCore.Irr ↥S :=
  (Classical.choose_spec (Classical.choose_spec
    (Work.BrauerSuzuki.Quaternion.characters d))).1

theorem th_mem_Irr (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    th S d ∈ Work.CharCore.Irr ↥S :=
  (Classical.choose_spec (Classical.choose_spec
    (Work.BrauerSuzuki.Quaternion.characters d))).2.1

theorem lam_ne_th (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    lam S d ≠ th S d :=
  (Classical.choose_spec (Classical.choose_spec
    (Work.BrauerSuzuki.Quaternion.characters d))).2.2.1

theorem lam_ne_one (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    lam S d ≠ (fun _ => (1 : ℂ)) :=
  (Classical.choose_spec (Classical.choose_spec
    (Work.BrauerSuzuki.Quaternion.characters d))).2.2.2.1

theorem th_ne_one (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    th S d ≠ (fun _ => (1 : ℂ)) :=
  (Classical.choose_spec (Classical.choose_spec
    (Work.BrauerSuzuki.Quaternion.characters d))).2.2.2.2.1

/-- `λ = 1` on `⟨τ⟩` (Dade (6.3)). -/
theorem lam_apply_mem_zpowers (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) {x : ↥S}
    (hx : x ∈ Subgroup.zpowers d.tau) : lam S d x = 1 :=
  (Classical.choose_spec (Classical.choose_spec
    (Work.BrauerSuzuki.Quaternion.characters d))).2.2.2.2.2.1 x hx

/-- `λ 1 = 1`. -/
theorem lam_apply_one (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    lam S d 1 = 1 :=
  lam_apply_mem_zpowers S d (Subgroup.one_mem _)

/-- `θ 1 = 2` (Dade (6.5)). -/
theorem th_apply_one (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) :
    th S d 1 = 2 :=
  (Classical.choose_spec (Classical.choose_spec
    (Work.BrauerSuzuki.Quaternion.characters d))).2.2.2.2.2.2.2.1

/-- The four-case table for `1 + λ - θ` (Dade (6.7)), first case: it vanishes off `⟨τ⟩`. -/
theorem one_add_lam_sub_th_notMem (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) {x : ↥S}
    (hx : x ∉ Subgroup.zpowers d.tau) : (1 : ℂ) + lam S d x - th S d x = 0 :=
  (Classical.choose_spec (Classical.choose_spec
    (Work.BrauerSuzuki.Quaternion.characters d))).2.2.2.2.2.2.2.2.2.2.1 x hx

/-- Second case of the table: `= 2` on `⟨τ⟩ \ ⟨τ²⟩`. -/
theorem one_add_lam_sub_th_two (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) {x : ↥S}
    (hx : x ∈ Subgroup.zpowers d.tau) (hx2 : x ∉ Subgroup.zpowers (d.tau ^ 2)) :
    (1 : ℂ) + lam S d x - th S d x = 2 :=
  (Classical.choose_spec (Classical.choose_spec
    (Work.BrauerSuzuki.Quaternion.characters d))).2.2.2.2.2.2.2.2.2.2.2.1 x hx hx2

/-- Third case of the table: `= 4` on `⟨τ²⟩ \ ⟨τ⁴⟩`. -/
theorem one_add_lam_sub_th_four (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) {x : ↥S}
    (hx : x ∈ Subgroup.zpowers (d.tau ^ 2)) (hx4 : x ∉ Subgroup.zpowers (d.tau ^ 4)) :
    (1 : ℂ) + lam S d x - th S d x = 4 :=
  (Classical.choose_spec (Classical.choose_spec
    (Work.BrauerSuzuki.Quaternion.characters d))).2.2.2.2.2.2.2.2.2.2.2.2.1 x hx hx4

/-- Fourth case of the table: `= 0` on `⟨τ⁴⟩`. -/
theorem one_add_lam_sub_th_zpow_four (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) {x : ↥S}
    (hx : x ∈ Subgroup.zpowers (d.tau ^ 4)) : (1 : ℂ) + lam S d x - th S d x = 0 :=
  (Classical.choose_spec (Classical.choose_spec
    (Work.BrauerSuzuki.Quaternion.characters d))).2.2.2.2.2.2.2.2.2.2.2.2.2 x hx

/-- The virtual character `α = (1 + λ - θ) ∘ φ` of `H = N_G(⟨σ⟩)` (Dade's Theorem 6.8). -/
noncomputable def alpha (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) : ↥(Hsub S d) → ℂ :=
  Work.Induction.resFunHom (phi S d hn) (fun x => (1 : ℂ) + lam S d x - th S d x)

@[simp] theorem alpha_apply (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) (h : ↥(Hsub S d)) :
    alpha S d hn h = (1 : ℂ) + lam S d (phi S d hn h) - th S d (phi S d hn h) := rfl

end Work.BrauerSuzuki.Dade
