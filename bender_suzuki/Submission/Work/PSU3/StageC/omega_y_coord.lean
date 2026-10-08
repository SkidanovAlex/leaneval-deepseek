import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.GaloisField
import Submission.Work.PSU3.FMap
import Submission.Work.PSU3.StageB.Frame
import Submission.Work.PSU3.StageB.Canon
import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.RankOneUniqueness.canon_exists
import Submission.Work.RankOneUniqueness.canon_unique
import Submission.Work.PSU3.RankOne.H16
import Submission.Work.PSU3.RankOne.canon_conj
import Submission.Work.PSU3.RankOne.canon_mul
import Submission.Work.PSU3.StageC.e_zc_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness

namespace Work.PSU3.StageC

open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## Elementary frame facts -/

/-- `s = zc 1` as an element of `Q`. -/
noncomputable def ssQ (fr : CoarseFrame H Q t n) : Q :=
  ⟨fr.zc 1, fr.Q0_le (fr.zc_mem 1 (by simp))⟩

@[simp] lemma ssQ_coe (fr : CoarseFrame H Q t n) : ((ssQ fr : Q) : G) = fr.zc 1 := rfl

lemma ssQ_ne_one (fr : CoarseFrame H Q t n) : (ssQ fr : Q) ≠ 1 :=
  fun h => StageB.frameS_ne_one fr (by simpa [StageB.frameS] using congrArg (fun z : Q => (z : G)) h)

lemma ssQ_coe_ne_one (fr : CoarseFrame H Q t n) : ((ssQ fr : Q) : G) ≠ 1 :=
  fun h => ssQ_ne_one fr (Subtype.ext h)

lemma one_mem_Q0 (fr : CoarseFrame H Q t n) : (1 : G) ∈ fr.Q0 :=
  (fr.mem_Q0_iff 1 Q.one_mem).mpr (by simp)

/-- The canonical data of `s = zc 1`: `f(s) = g(s) = s`, `h(s) = 1`. -/
lemma canon_ssQ (hsplit : IsSplitRankOne H Q t) (fr : CoarseFrame H Q t n) :
    (fcan hsplit (ssQ fr) : G) = fr.zc 1 ∧ (gcan hsplit (ssQ fr) : G) = fr.zc 1 ∧
      (hcan hsplit (ssQ fr) : G) = 1 := by
  have hne : ((ssQ fr : Q) : G) ≠ 1 := ssQ_coe_ne_one fr
  have hcanon : t * ((ssQ fr : Q) : G) * t = ((ssQ fr : Q) : G) * (1 : G) * t * ((ssQ fr : Q) : G) := by
    show t * fr.zc 1 * t = fr.zc 1 * (1 : G) * t * fr.zc 1
    rw [mul_one]; exact fr.s_struct
  have key := Work.PSU3.StageB.canon_unique'' hsplit hne
    (g := ssQ fr) (d := 1) (y := ssQ fr) hcanon
  exact ⟨key.2.2.symm, key.1.symm, key.2.1.symm⟩

/-! ## Conjugation by `t` -/

lemma t_conj_of_comm (hsplit : IsSplitRankOne H Q t) {a : G} (ha : a * t = t * a) :
    t * a * t = a := by
  rw [← ha, mul_assoc, mul_self_eq_one hsplit, mul_one]

lemma zeta_comm_t (hsplit : IsSplitRankOne H Q t) (fr : CoarseFrame H Q t n) :
    t * (fr.ζ : G) = (fr.ζ : G) * t :=
  (Subgroup.mem_centralizer_iff.mp
    (Subgroup.mem_inf.mp (Work.ThmF.W_le_centD H t fr.ζ_mem_W)).2) t (by simp)

private lemma t_conj_zeta (hsplit : IsSplitRankOne H Q t) (fr : CoarseFrame H Q t n) :
    t * (fr.ζ : G) * t = (fr.ζ : G) :=
  t_conj_of_comm hsplit (zeta_comm_t hsplit fr).symm

lemma t_conj_zeta_inv (hsplit : IsSplitRankOne H Q t) (fr : CoarseFrame H Q t n) :
    t * (fr.ζ : G)⁻¹ * t = (fr.ζ : G)⁻¹ := by
  have hc : Commute (t : G) ((fr.ζ : G)⁻¹) :=
    Commute.inv_right (zeta_comm_t hsplit fr)
  rw [hc.eq, mul_assoc, mul_self_eq_one hsplit, mul_one]

lemma t_conj_zeta_sq_inv (hsplit : IsSplitRankOne H Q t) (fr : CoarseFrame H Q t n) :
    t * ((fr.ζ : G) ^ 2)⁻¹ * t = ((fr.ζ : G) ^ 2)⁻¹ := by
  have hc : Commute (t : G) (((fr.ζ : G) ^ 2)⁻¹) :=
    Commute.inv_right (Commute.pow_right (zeta_comm_t hsplit fr) 2)
  rw [hc.eq, mul_assoc, mul_self_eq_one hsplit, mul_one]

/-- `f(x^a) = (t a t)⁻¹ f(x) (t a t)` in the form used below. -/
lemma fcan_conjG (hsplit : IsSplitRankOne H Q t) {x : Q} (hx : (x : G) ≠ 1)
    {a : G} (haD : a ∈ twoPoint H t) {w : Q} (hw : (w : G) = a⁻¹ * (x : G) * a) :
    (fcan hsplit w : G) = (t * a * t)⁻¹ * (fcan hsplit x : G) * (t * a * t) := by
  obtain ⟨xa, hxa, hf, -, -⟩ :=
    Work.PSU3.StageB.canon_conj_fun hsplit hx (⟨a, haD⟩ : ↥(twoPoint H t))
  have hEq : xa = w := by
    apply Subtype.ext
    rw [hxa, hw]
  rw [← hEq]
  simpa using hf

theorem omega_h_eq (hsplit : IsSplitRankOne H Q t) (fr : CoarseFrame H Q t n)
    {ω g hh : G} (hωQ : ω ∈ Q) (hω0 : ω ∉ fr.Q0) (hgQ : g ∈ Q) (hhW : hh ∈ W H t)
    (hrel : t * ω * t = g * hh * t * ((fr.ζ : G)⁻¹ * ω⁻¹ * (fr.ζ : G))) :
    hh = (fr.ζ : G) ^ 3 := by
  have hωne : ω ≠ 1 := fun h => hω0 (h ▸ one_mem_Q0 fr)
  have hω0inv : ω⁻¹ ∉ fr.Q0 := fun h => hω0 (by simpa using (fr.Q0).inv_mem h)
  have hhD : hh ∈ twoPoint H t := (Subgroup.mem_inf.mp (Work.ThmF.W_le_centD H t hhW)).1
  have hzD : (fr.ζ : G) ∈ twoPoint H t := fr.KW_le fr.ζ.2
  have hzinvD : (fr.ζ : G)⁻¹ ∈ twoPoint H t := (twoPoint H t).inv_mem hzD
  have hzsqinvD : ((fr.ζ : G) ^ 2)⁻¹ ∈ twoPoint H t :=
    (twoPoint H t).inv_mem ((twoPoint H t).pow_mem hzD 2)
  have hzH : (fr.ζ : G) ∈ H := twoPoint_le_left H t hzD
  have hwQ : (fr.ζ : G)⁻¹ * ω⁻¹ * (fr.ζ : G) ∈ Q := by
    simpa using conj_mem_of_mem hsplit (H.inv_mem hzH) (Q.inv_mem hωQ)
  have hωne' : ((⟨ω, hωQ⟩ : Q) : G) ≠ 1 := hωne
  -- canonical data of `ω`
  have key := Work.PSU3.StageB.canon_unique'' hsplit (x := (⟨ω, hωQ⟩ : Q)) hωne'
    (g := ⟨g, hgQ⟩) (d := ⟨hh, hhD⟩)
    (y := ⟨(fr.ζ : G)⁻¹ * ω⁻¹ * (fr.ζ : G), hwQ⟩)
    (by simpa using hrel)
  have hhcan : (hcan hsplit (⟨ω, hωQ⟩ : Q) : G) = hh := key.2.1.symm
  have hfcan : (fcan hsplit (⟨ω, hωQ⟩ : Q) : G) = (fr.ζ : G)⁻¹ * ω⁻¹ * (fr.ζ : G) := key.2.2.symm
  have hxinv : (((⟨ω, hωQ⟩ : Q)⁻¹) : G) = ω⁻¹ := rfl
  have hxinvne : (((⟨ω, hωQ⟩ : Q)⁻¹) : G) ≠ 1 := by
    rw [hxinv]
    exact fun h => hω0inv (h ▸ one_mem_Q0 fr)
  -- `f(ω⁻¹) = ζ ω ζ⁻¹`
  have ht1 : (fcan hsplit ((⟨ω, hωQ⟩ : Q)⁻¹) : G) = (fr.ζ : G) * ω * (fr.ζ : G)⁻¹ := by
    have hff : (fcan hsplit (fcan hsplit (⟨ω, hωQ⟩ : Q)) : G) = ω := (fcan_fcan hsplit hωne').1
    have hconj := fcan_conjG hsplit (x := (⟨ω, hωQ⟩ : Q)⁻¹) hxinvne
      hzD (w := fcan hsplit (⟨ω, hωQ⟩ : Q)) (by rw [hfcan]; rfl)
    rw [hff, t_conj_zeta hsplit fr] at hconj
    calc (fcan hsplit ((⟨ω, hωQ⟩ : Q)⁻¹) : G)
        = (fr.ζ : G) * ((fr.ζ : G)⁻¹ * (fcan hsplit ((⟨ω, hωQ⟩ : Q)⁻¹) : G) * (fr.ζ : G)) *
            (fr.ζ : G)⁻¹ := by group
      _ = (fr.ζ : G) * ω * (fr.ζ : G)⁻¹ := by rw [hconj.symm]
  -- `f((f(ω⁻¹))⁻¹) = ζ² ω ζ⁻²`
  have ht2 : (fcan hsplit ((fcan hsplit ((⟨ω, hωQ⟩ : Q)⁻¹))⁻¹) : G)
      = (fr.ζ : G) ^ 2 * ω * ((fr.ζ : G) ^ 2)⁻¹ := by
    have hw : (((fcan hsplit ((⟨ω, hωQ⟩ : Q)⁻¹))⁻¹ : Q) : G)
        = (fr.ζ : G)⁻¹⁻¹ * ω⁻¹ * (fr.ζ : G)⁻¹ := by
      rw [Subgroup.coe_inv, ht1, hxinv]
      show ((fr.ζ : G) * ω * (fr.ζ : G)⁻¹)⁻¹ = (fr.ζ : G)⁻¹⁻¹ * ω⁻¹ * (fr.ζ : G)⁻¹
      group
    have hconj := fcan_conjG hsplit (x := (⟨ω, hωQ⟩ : Q)⁻¹) hxinvne
      hzinvD (w := (fcan hsplit ((⟨ω, hωQ⟩ : Q)⁻¹))⁻¹) hw
    rw [t_conj_zeta_inv hsplit fr] at hconj
    rw [ht1] at hconj
    rw [hconj]
    simp only [pow_two, mul_inv_rev, inv_inv]
    group
  -- `f((f((f(ω⁻¹))⁻¹))⁻¹) = ζ³ ω ζ⁻³`
  have ht3 : (fcan hsplit ((fcan hsplit ((fcan hsplit ((⟨ω, hωQ⟩ : Q)⁻¹))⁻¹))⁻¹) : G)
      = (fr.ζ : G) ^ 3 * ω * ((fr.ζ : G) ^ 3)⁻¹ := by
    have hw : (((fcan hsplit ((fcan hsplit ((⟨ω, hωQ⟩ : Q)⁻¹))⁻¹))⁻¹ : Q) : G)
        = (((fr.ζ : G) ^ 2)⁻¹)⁻¹ * ω⁻¹ * ((fr.ζ : G) ^ 2)⁻¹ := by
      rw [Subgroup.coe_inv, ht2, hxinv]
      show (((fr.ζ : G) ^ 2 * ω * ((fr.ζ : G) ^ 2)⁻¹))⁻¹
          = (((fr.ζ : G) ^ 2)⁻¹)⁻¹ * ω⁻¹ * ((fr.ζ : G) ^ 2)⁻¹
      group
    have hconj := fcan_conjG hsplit (x := (⟨ω, hωQ⟩ : Q)⁻¹) hxinvne
      hzsqinvD (w := (fcan hsplit ((fcan hsplit ((⟨ω, hωQ⟩ : Q)⁻¹))⁻¹))⁻¹) hw
    rw [t_conj_zeta_sq_inv hsplit fr] at hconj
    rw [ht1] at hconj
    rw [hconj]
    group
  have hjj := fcan_jjj hsplit hωne'
  rw [ht3, hhcan] at hjj
  -- hjj : ζ³ ω ζ⁻³ = hh ω hh⁻¹
  have hcentral : (((fr.ζ : G) ^ 3)⁻¹ * hh) * ω * (((fr.ζ : G) ^ 3)⁻¹ * hh)⁻¹ = ω := by
    have h1 : (((fr.ζ : G) ^ 3)⁻¹ * hh) * ω * (((fr.ζ : G) ^ 3)⁻¹ * hh)⁻¹
        = ((fr.ζ : G) ^ 3)⁻¹ * (hh * ω * hh⁻¹) * (fr.ζ : G) ^ 3 := by group
    rw [h1, ← hjj]
    group
  have huW : ((fr.ζ : G) ^ 3)⁻¹ * hh ∈ W H t :=
    (W H t).mul_mem ((W H t).inv_mem ((W H t).pow_mem fr.ζ_mem_W 3)) hhW
  have huω : (((fr.ζ : G) ^ 3)⁻¹ * hh) * ω = ω * (((fr.ζ : G) ^ 3)⁻¹ * hh) := by
    calc (((fr.ζ : G) ^ 3)⁻¹ * hh) * ω
        = ((((fr.ζ : G) ^ 3)⁻¹ * hh) * ω * (((fr.ζ : G) ^ 3)⁻¹ * hh)⁻¹) * (((fr.ζ : G) ^ 3)⁻¹ * hh) := by
          group
      _ = ω * (((fr.ζ : G) ^ 3)⁻¹ * hh) := by rw [hcentral]
  have hu1 : ((fr.ζ : G) ^ 3)⁻¹ * hh = 1 := by
    by_contra hne
    exact hω0 (fr.W_semireg _ huW hne ω hωQ huω)
  calc hh = (fr.ζ : G) ^ 3 * (((fr.ζ : G) ^ 3)⁻¹ * hh) := by group
    _ = (fr.ζ : G) ^ 3 := by rw [hu1, mul_one]

/-! ## `s = zc 1` and `ζ` -/

lemma zeta_s_comm (fr : CoarseFrame H Q t n) :
    (fr.ζ : G) * fr.zc 1 = fr.zc 1 * (fr.ζ : G) := by
  have h := fr.act_zc_ζ 1 (by simp)
  have h2 : (fr.ζ : G) * ((fr.ζ : G)⁻¹ * fr.zc 1 * (fr.ζ : G)) = (fr.ζ : G) * fr.zc 1 := by rw [h]
  simpa [mul_assoc] using h2.symm

lemma zeta_s_conj (fr : CoarseFrame H Q t n) :
    (fr.ζ : G) * fr.zc 1 * (fr.ζ : G)⁻¹ = fr.zc 1 :=
  by rw [zeta_s_comm fr, mul_assoc, mul_inv_cancel, mul_one]

lemma zeta_inv_s_conj (fr : CoarseFrame H Q t n) :
    (fr.ζ : G)⁻¹ * fr.zc 1 * (fr.ζ : G) = fr.zc 1 := fr.act_zc_ζ 1 (by simp)

/-- From the `Ω`-relation, the canonical data of `ω` and `ω⁻¹`. -/
lemma canon_omega_inv (hsplit : IsSplitRankOne H Q t) (fr : CoarseFrame H Q t n)
    {ω g hh : G} (hωQ : ω ∈ Q) (hω0 : ω ∉ fr.Q0) (hgQ : g ∈ Q) (hhD : hh ∈ twoPoint H t)
    (hrel : t * ω * t = g * hh * t * ((fr.ζ : G)⁻¹ * ω⁻¹) * (fr.ζ : G)) :
    (hcan hsplit (⟨ω, hωQ⟩ : Q) : G) = hh ∧
    (fcan hsplit (⟨ω, hωQ⟩ : Q) : G) = (fr.ζ : G)⁻¹ * ω⁻¹ * (fr.ζ : G) ∧
    (fcan hsplit ((⟨ω, hωQ⟩ : Q)⁻¹) : G) = (fr.ζ : G) * ω * (fr.ζ : G)⁻¹ ∧
    (gcan hsplit ((⟨ω, hωQ⟩ : Q)⁻¹) : G) = (fr.ζ : G)⁻¹ * ω * (fr.ζ : G) := by
  have hrel' : t * ω * t = g * hh * t * ((fr.ζ : G)⁻¹ * ω⁻¹ * (fr.ζ : G)) := by
    rw [hrel]; group
  have hωne : ω ≠ 1 := fun h => hω0 (h ▸ one_mem_Q0 fr)
  have hω0inv : ω⁻¹ ∉ fr.Q0 := fun h => hω0 (by simpa using (fr.Q0).inv_mem h)
  have hzH : (fr.ζ : G) ∈ H := twoPoint_le_left H t (fr.KW_le fr.ζ.2)
  have hwQ : (fr.ζ : G)⁻¹ * ω⁻¹ * (fr.ζ : G) ∈ Q := by
    simpa using conj_mem_of_mem hsplit (H.inv_mem hzH) (Q.inv_mem hωQ)
  have hωne' : ((⟨ω, hωQ⟩ : Q) : G) ≠ 1 := hωne
  have key := Work.PSU3.StageB.canon_unique'' hsplit (x := (⟨ω, hωQ⟩ : Q)) hωne'
    (g := ⟨g, hgQ⟩) (d := ⟨hh, hhD⟩)
    (y := ⟨(fr.ζ : G)⁻¹ * ω⁻¹ * (fr.ζ : G), hwQ⟩)
    (by simpa using hrel')
  have hhcan : (hcan hsplit (⟨ω, hωQ⟩ : Q) : G) = hh := key.2.1.symm
  have hfcan : (fcan hsplit (⟨ω, hωQ⟩ : Q) : G) = (fr.ζ : G)⁻¹ * ω⁻¹ * (fr.ζ : G) := key.2.2.symm
  have hxinvne : (((⟨ω, hωQ⟩ : Q)⁻¹) : G) ≠ 1 := by
    have hxinv : (((⟨ω, hωQ⟩ : Q)⁻¹) : G) = ω⁻¹ := rfl
    rw [hxinv]
    exact fun h => hω0inv (h ▸ one_mem_Q0 fr)
  have ht1 : (fcan hsplit ((⟨ω, hωQ⟩ : Q)⁻¹) : G) = (fr.ζ : G) * ω * (fr.ζ : G)⁻¹ := by
    have hff : (fcan hsplit (fcan hsplit (⟨ω, hωQ⟩ : Q)) : G) = ω := (fcan_fcan hsplit hωne').1
    have hconj := fcan_conjG hsplit (x := (⟨ω, hωQ⟩ : Q)⁻¹) hxinvne
      (fr.KW_le fr.ζ.2) (w := fcan hsplit (⟨ω, hωQ⟩ : Q)) (by rw [hfcan]; rfl)
    rw [hff, t_conj_zeta hsplit fr] at hconj
    calc (fcan hsplit ((⟨ω, hωQ⟩ : Q)⁻¹) : G)
        = (fr.ζ : G) * ((fr.ζ : G)⁻¹ * (fcan hsplit ((⟨ω, hωQ⟩ : Q)⁻¹) : G) * (fr.ζ : G)) *
            (fr.ζ : G)⁻¹ := by group
      _ = (fr.ζ : G) * ω * (fr.ζ : G)⁻¹ := by rw [hconj.symm]
  have hg1 : (gcan hsplit ((⟨ω, hωQ⟩ : Q)⁻¹) : G) = (fr.ζ : G)⁻¹ * ω * (fr.ζ : G) := by
    rw [gcan_inv hsplit hωne', hfcan]
    group
  exact ⟨hhcan, hfcan, ht1, hg1⟩

theorem omega_s_identity (hsplit : IsSplitRankOne H Q t) (fr : CoarseFrame H Q t n)
    {ω g hh : G} (hωQ : ω ∈ Q) (hω0 : ω ∉ fr.Q0) (hgQ : g ∈ Q) (hhW : hh ∈ W H t)
    (hhζ : hh = (fr.ζ : G) ^ 3)
    (hrel : t * ω * t = g * hh * t * ((fr.ζ : G)⁻¹ * ω⁻¹) * (fr.ζ : G)) :
    ∃ A ∈ Q, (fr.ζ : G) * A * (fr.ζ : G)⁻¹ * fr.zc 1
      = (fr.ζ : G) ^ 2 * A * ((fr.ζ : G) ^ 2)⁻¹ * ((fr.ζ : G) * ω * (fr.ζ : G)⁻¹) := by
  have hhD : hh ∈ twoPoint H t := (Subgroup.mem_inf.mp (Work.ThmF.W_le_centD H t hhW)).1
  have hh_comm : hh * t = t * hh :=
    ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (Work.ThmF.W_le_centD H t hhW)).2)
      t (by simp)).symm
  have hhTinv : t * hh⁻¹ * t = hh⁻¹ := by
    have hc : Commute (hh⁻¹ : G) t := Commute.inv_left hh_comm
    exact t_conj_of_comm hsplit hc.eq
  have hωne : ω ≠ 1 := fun h => hω0 (h ▸ one_mem_Q0 fr)
  have hω0inv : ω⁻¹ ∉ fr.Q0 := fun h => hω0 (by simpa using (fr.Q0).inv_mem h)
  have hcd := canon_omega_inv hsplit fr hωQ hω0 hgQ hhD hrel
  have hhcan : (hcan hsplit (⟨ω, hωQ⟩ : Q) : G) = hh := hcd.1
  have hfcaninv : (fcan hsplit ((⟨ω, hωQ⟩ : Q)⁻¹) : G) = (fr.ζ : G) * ω * (fr.ζ : G)⁻¹ := hcd.2.2.1
  have hgcaninv : (gcan hsplit ((⟨ω, hωQ⟩ : Q)⁻¹) : G) = (fr.ζ : G)⁻¹ * ω * (fr.ζ : G) := hcd.2.2.2
  have hxwne : ((⟨ω, hωQ⟩ : Q) : G) ≠ 1 := hωne
  have hζD : (fr.ζ : G) ∈ twoPoint H t := fr.KW_le fr.ζ.2
  have hεD : (fr.ζ : G)⁻¹ ∈ twoPoint H t := (twoPoint H t).inv_mem hζD
  have hxne : (((⟨ω, hωQ⟩ : Q)⁻¹) : G) ≠ 1 := by
    have hxinv : (((⟨ω, hωQ⟩ : Q)⁻¹) : G) = ω⁻¹ := rfl
    rw [hxinv]; exact fun h => hω0inv (h ▸ one_mem_Q0 fr)
  have hssne : ((ssQ fr : Q) : G) ≠ 1 := ssQ_coe_ne_one fr
  have cs := canon_ssQ hsplit fr
  have csF : fcan hsplit (ssQ fr) = ssQ fr := Subtype.ext cs.1
  have csG : gcan hsplit (ssQ fr) = ssQ fr := Subtype.ext cs.2.1
  have csH : (hcan hsplit (ssQ fr) : G) = 1 := cs.2.2
  have hzinQ : (fr.zc 1) ∈ fr.Q0 := fr.zc_mem 1 (by simp)
  have hXne : (((⟨ω, hωQ⟩ : Q) * ssQ fr : Q) : G) ≠ 1 := by
    intro h
    apply hω0
    have h2 : (ω : G) = (fr.zc 1)⁻¹ := by
      have hh1 : (ω : G) * fr.zc 1 = 1 := by
        simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h
      calc (ω : G) = (ω * fr.zc 1) * (fr.zc 1)⁻¹ := by group
        _ = 1 * (fr.zc 1)⁻¹ := by rw [hh1]
        _ = (fr.zc 1)⁻¹ := one_mul _
    rw [h2]; exact (fr.Q0).inv_mem hzinQ
  have hU1ne : ((((⟨ω, hωQ⟩ : Q)⁻¹) * ssQ fr : Q) : G) ≠ 1 := by
    intro h
    apply hω0inv
    have h2 : (ω⁻¹ : G) = (fr.zc 1)⁻¹ := by
      have hh1 : (ω⁻¹ : G) * fr.zc 1 = 1 := by
        simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h
      calc (ω⁻¹ : G) = (ω⁻¹ * fr.zc 1) * (fr.zc 1)⁻¹ := by group
        _ = 1 * (fr.zc 1)⁻¹ := by rw [hh1]
        _ = (fr.zc 1)⁻¹ := one_mul _
    rw [h2]; exact (fr.Q0).inv_mem hzinQ
  have hU2ne : ((ssQ fr * ((⟨ω, hωQ⟩ : Q)⁻¹) : Q) : G) ≠ 1 := by
    intro h
    apply hω0inv
    have h2 : (ω⁻¹ : G) = (fr.zc 1)⁻¹ := by
      have hh1 : fr.zc 1 * (ω⁻¹ : G) = 1 := by
        simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h
      calc (ω⁻¹ : G) = (fr.zc 1)⁻¹ * (fr.zc 1 * ω⁻¹) := by group
        _ = (fr.zc 1)⁻¹ * 1 := by rw [hh1]
        _ = (fr.zc 1)⁻¹ := mul_one _
    rw [h2]; exact (fr.Q0).inv_mem hzinQ
  -- H6 with `x = ω⁻¹`, `y = s`
  have h6a := (canon_mul_fun hsplit hxne hssne hU1ne).1
  rw [csH, csF, csG] at h6a
  rw [show t * (1 : G) * t = 1 from by rw [mul_one, mul_self_eq_one hsplit]] at h6a
  simp only [inv_one, one_mul, mul_one, ssQ_coe] at h6a
  have hFA : (fcan hsplit ((fcan hsplit ((⟨ω, hωQ⟩ : Q)⁻¹)) * ssQ fr) : G)
      = (fr.ζ : G) * (fcan hsplit ((⟨ω, hωQ⟩ : Q) * ssQ fr) : G) * (fr.ζ : G)⁻¹ := by
    have hcoea : ((fcan hsplit ((⟨ω, hωQ⟩ : Q)⁻¹) * ssQ fr : Q) : G)
        = ((fr.ζ : G) * ω * (fr.ζ : G)⁻¹) * fr.zc 1 := by
      rw [Subgroup.coe_mul, hfcaninv, ssQ_coe]
    have hcoeb : (((⟨ω, hωQ⟩ : Q) * ssQ fr : Q) : G) = ω * fr.zc 1 := by
      rw [Subgroup.coe_mul, ssQ_coe]
    have hw : ((fcan hsplit ((⟨ω, hωQ⟩ : Q)⁻¹) * ssQ fr : Q) : G)
        = ((fr.ζ : G)⁻¹)⁻¹ * (((⟨ω, hωQ⟩ : Q) * ssQ fr : Q) : G) * (fr.ζ : G)⁻¹ := by
      rw [hcoea, hcoeb, inv_inv]
      rw [show (fr.ζ : G) * (ω * fr.zc 1) * (fr.ζ : G)⁻¹
          = ((fr.ζ : G) * ω * (fr.ζ : G)⁻¹) * ((fr.ζ : G) * fr.zc 1 * (fr.ζ : G)⁻¹) from by group,
        zeta_s_conj fr]
    have h := fcan_conjG hsplit hXne hεD (w := fcan hsplit ((⟨ω, hωQ⟩ : Q)⁻¹) * ssQ fr) hw
    rw [t_conj_zeta_inv hsplit fr] at h
    simpa using h
  rw [hFA] at h6a
  -- H6 with `x = s`, `y = ω⁻¹`
  have hhinv : (hcan hsplit ((⟨ω, hωQ⟩ : Q)⁻¹) : G) = hh⁻¹ := by
    rw [hcan_inv hsplit hxwne, hhcan]
    exact hhTinv
  have h6b := (canon_mul_fun hsplit hssne hxne hU2ne).1
  rw [csF, hhinv, hhTinv, inv_inv, hfcaninv] at h6b
  have hFB : (fcan hsplit (ssQ fr * gcan hsplit ((⟨ω, hωQ⟩ : Q)⁻¹)) : G)
      = (fr.ζ : G)⁻¹ * (fcan hsplit ((⟨ω, hωQ⟩ : Q) * ssQ fr) : G) * (fr.ζ : G) := by
    have hcoea : ((ssQ fr * gcan hsplit ((⟨ω, hωQ⟩ : Q)⁻¹) : Q) : G)
        = fr.zc 1 * ((fr.ζ : G)⁻¹ * ω * (fr.ζ : G)) := by
      rw [Subgroup.coe_mul, ssQ_coe, hgcaninv]
    have hcoeb : (((⟨ω, hωQ⟩ : Q) * ssQ fr : Q) : G) = ω * fr.zc 1 := by
      rw [Subgroup.coe_mul, ssQ_coe]
    have hwQ' : (fr.ζ : G)⁻¹ * ω * (fr.ζ : G) ∈ Q := by
      have hzH : (fr.ζ : G) ∈ H := twoPoint_le_left H t hζD
      simpa using conj_mem_of_mem hsplit (H.inv_mem hzH) hωQ
    have hw : ((ssQ fr * gcan hsplit ((⟨ω, hωQ⟩ : Q)⁻¹) : Q) : G)
        = (fr.ζ : G)⁻¹ * (((⟨ω, hωQ⟩ : Q) * ssQ fr : Q) : G) * (fr.ζ : G) := by
      rw [hcoea, hcoeb]
      rw [show (fr.ζ : G)⁻¹ * (ω * fr.zc 1) * (fr.ζ : G)
          = ((fr.ζ : G)⁻¹ * ω * (fr.ζ : G)) * ((fr.ζ : G)⁻¹ * fr.zc 1 * (fr.ζ : G)) from by group,
        zeta_inv_s_conj fr]
      exact fr.Q0_central (fr.zc 1) hzinQ ((fr.ζ : G)⁻¹ * ω * (fr.ζ : G)) hwQ'
    have h := fcan_conjG hsplit hXne hζD (w := ssQ fr * gcan hsplit ((⟨ω, hωQ⟩ : Q)⁻¹)) hw
    rw [t_conj_zeta hsplit fr] at h
    simpa using h
  rw [hFB] at h6b
  -- the two expressions agree
  have hUeq : (((⟨ω, hωQ⟩ : Q)⁻¹) * ssQ fr) = ssQ fr * ((⟨ω, hωQ⟩ : Q)⁻¹) := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ssQ_coe]
    exact (fr.Q0_central (fr.zc 1) hzinQ ((⟨ω, hωQ⟩ : Q)⁻¹) (Q.inv_mem hωQ)).symm
  refine ⟨(fcan hsplit ((⟨ω, hωQ⟩ : Q) * ssQ fr) : G),
    (fcan hsplit ((⟨ω, hωQ⟩ : Q) * ssQ fr)).2, ?_⟩
  have e2' : (fcan hsplit (((⟨ω, hωQ⟩ : Q)⁻¹) * ssQ fr) : G)
      = (fr.ζ : G) ^ 2 * (fcan hsplit ((⟨ω, hωQ⟩ : Q) * ssQ fr) : G)
          * ((fr.ζ : G) ^ 2)⁻¹ * ((fr.ζ : G) * ω * (fr.ζ : G)⁻¹) := by
    rw [hUeq]
    rw [h6b, hhζ]
    group
  rw [← h6a, e2']

/-! ## The coordinate evaluation -/

lemma omega_y_coord_aux {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : PSU3Hyp H Q t) {n : ℕ} (fr : CoarseFrame H Q t n) {ω : G}
    (hωQ : ω ∈ Q)
    (hsq : ∀ a : (E n)ˣ, σE (a : E n) = a → (fr.nm a : E n) = (a : E n) ^ 2)
    (hω2 : ω ^ 2 = fr.zc ((fr.κ fr.ζ : E n) + (fr.κ fr.ζ : E n)⁻¹))
    (e : Q ≃* SZ (E n)) (μ : (E n)ˣ)
    (hex : ∀ x : Q, (e x).x = (μ : E n) * Multiplicative.toAdd (fr.bar x))
    (hes : ∀ hs : fr.zc 1 ∈ Q, (e ⟨fr.zc 1, hs⟩).x = 0 ∧ (e ⟨fr.zc 1, hs⟩).y = 1)
    (heq : ∀ (d : fr.KW) (x y : Q), (y : G) = (d : G)⁻¹ * x * d →
      e y = SZ.torusAct (fr.κ d) (e x))
    {A : G} (hAQ : A ∈ Q)
    (hAid : (fr.ζ : G) * A * (fr.ζ : G)⁻¹ * fr.zc 1
      = (fr.ζ : G) ^ 2 * A * ((fr.ζ : G) ^ 2)⁻¹ * ((fr.ζ : G) * ω * (fr.ζ : G)⁻¹)) :
    (e ⟨ω, hωQ⟩).y = (((fr.κ fr.ζ : (E n)ˣ) : E n))⁻¹ := by
  classical
  have hsplit : IsSplitRankOne H Q t := hS.split
  set c : E n := ((fr.κ fr.ζ : (E n)ˣ) : E n) with hc
  have hc'' : ((fr.κ fr.ζ : (E n)ˣ) : E n) = c := hc.symm
  -- ### the norm equation
  have hσc : σE c = c⁻¹ := by
    rw [← hc'']
    exact eq_inv_of_mul_eq_one_right fr.ζ_norm
  have hσcinv : σE c⁻¹ = c := by rw [map_inv₀, hσc, inv_inv]
  have hσsqinv : σE ((c ^ 2)⁻¹) = c ^ 2 := by
    have h2 : ((c⁻¹) ^ 2)⁻¹ = c ^ 2 := by rw [inv_pow, inv_inv]
    rw [map_inv₀, map_pow, hσc]; exact h2
  have hcfix : σE (c + c⁻¹) = c + c⁻¹ := by rw [map_add, hσc, hσcinv, add_comm]
  have hc0 : c ≠ 0 := by rw [hc]; exact Units.ne_zero _
  have hcne1 : c ≠ 1 := by
    intro h
    have h1 : (fr.κ fr.ζ : (E n)ˣ) = 1 := by
      apply Units.ext
      rw [← hc''] at h
      simpa using h
    exact fr.ζ_ne_one (fr.κ_injective (by rw [h1, map_one]))
  -- e on `Q₀`
  let Z : Q := ⟨fr.zc (c + c⁻¹), fr.Q0_le (fr.zc_mem _ hcfix)⟩
  have hω2Q : (⟨ω, hωQ⟩ : Q) ^ 2 = Z := by
    apply Subtype.ext
    show ω ^ 2 = fr.zc (c + c⁻¹)
    rw [← hc'']; exact hω2
  have hZu : Z = ⟨fr.zc (c + c⁻¹), fr.Q0_le (fr.zc_mem (c + c⁻¹) hcfix)⟩ := rfl
  have hZ : (e Z).y = c + c⁻¹ := by
    rw [hZu]
    exact (Work.PSU3.StageC.e_zc_eq hS fr hsq e μ hex hes heq (c + c⁻¹) hcfix
      (fr.Q0_le (fr.zc_mem (c + c⁻¹) hcfix))).2
  have hsq2 : (e ((⟨ω, hωQ⟩ : Q) ^ 2)).y
      = (e ⟨ω, hωQ⟩).y + (e ⟨ω, hωQ⟩).y + (e ⟨ω, hωQ⟩).x * σE ((e ⟨ω, hωQ⟩).x) := by
    rw [map_pow, pow_two, SZ.mul_y]
  have hx0σ : (e ⟨ω, hωQ⟩).x * σE ((e ⟨ω, hωQ⟩).x) = c + c⁻¹ := by
    have h := hZ
    rw [← hω2Q, hsq2] at h
    rw [CharTwo.add_self_eq_zero, zero_add] at h
    exact h
  -- ### the frozen identity under `e`
  have hzH : (fr.ζ : G) ∈ H := twoPoint_le_left H t (fr.KW_le fr.ζ.2)
  have hALmem : (fr.ζ : G) * A * (fr.ζ : G)⁻¹ ∈ Q := conj_mem_of_mem hsplit hzH hAQ
  have hARmem : (fr.ζ : G) ^ 2 * A * ((fr.ζ : G) ^ 2)⁻¹ ∈ Q :=
    conj_mem_of_mem hsplit (H.pow_mem hzH 2) hAQ
  have hOGmem : (fr.ζ : G) * ω * (fr.ζ : G)⁻¹ ∈ Q := conj_mem_of_mem hsplit hzH hωQ
  have hLmem : (fr.ζ : G) * A * (fr.ζ : G)⁻¹ * fr.zc 1 ∈ Q :=
    Q.mul_mem hALmem (fr.Q0_le (fr.zc_mem 1 (by simp)))
  have hRmem : (fr.ζ : G) ^ 2 * A * ((fr.ζ : G) ^ 2)⁻¹ * ((fr.ζ : G) * ω * (fr.ζ : G)⁻¹) ∈ Q :=
    Q.mul_mem hARmem hOGmem
  have hLR : (⟨(fr.ζ : G) * A * (fr.ζ : G)⁻¹ * fr.zc 1, hLmem⟩ : Q)
      = ⟨(fr.ζ : G) ^ 2 * A * ((fr.ζ : G) ^ 2)⁻¹ * ((fr.ζ : G) * ω * (fr.ζ : G)⁻¹), hRmem⟩ :=
    Subtype.ext hAid
  have hone : (1 : E n) + σE (1 : E n) = (0 : E n) * σE (0 : E n) := by
    rw [map_one, map_zero, mul_zero]; exact CharTwo.add_self_eq_zero 1
  have hssQe : e (ssQ fr) = (⟨0, 1, hone⟩ : SZ (E n)) := by
    apply SZ.ext
    · exact (Work.PSU3.StageC.e_zc_eq hS fr hsq e μ hex hes heq 1 (map_one σE)
        (fr.Q0_le (fr.zc_mem 1 (by simp)))).1
    · exact (Work.PSU3.StageC.e_zc_eq hS fr hsq e μ hex hes heq 1 (map_one σE)
        (fr.Q0_le (fr.zc_mem 1 (by simp)))).2
  have hALe : e (⟨(fr.ζ : G) * A * (fr.ζ : G)⁻¹, hALmem⟩ : Q)
      = SZ.torusAct ((fr.κ fr.ζ)⁻¹) (e ⟨A, hAQ⟩) := by
    have h := heq (fr.ζ⁻¹ : fr.KW) (⟨A, hAQ⟩ : Q)
      (⟨(fr.ζ : G) * A * (fr.ζ : G)⁻¹, hALmem⟩ : Q) (by
        show (fr.ζ : G) * A * (fr.ζ : G)⁻¹ = (fr.ζ : G)⁻¹⁻¹ * A * (fr.ζ : G)⁻¹
        rw [inv_inv])
    simpa using h
  have hARe : e (⟨(fr.ζ : G) ^ 2 * A * ((fr.ζ : G) ^ 2)⁻¹, hARmem⟩ : Q)
      = SZ.torusAct (((fr.κ fr.ζ) ^ 2)⁻¹) (e ⟨A, hAQ⟩) := by
    have h := heq ((fr.ζ ^ 2)⁻¹ : fr.KW) (⟨A, hAQ⟩ : Q)
      (⟨(fr.ζ : G) ^ 2 * A * ((fr.ζ : G) ^ 2)⁻¹, hARmem⟩ : Q) (by
        show (fr.ζ : G) ^ 2 * A * ((fr.ζ : G) ^ 2)⁻¹
            = ((fr.ζ : G) ^ 2)⁻¹⁻¹ * A * ((fr.ζ : G) ^ 2)⁻¹
        rw [inv_inv])
    simpa [map_inv, map_pow] using h
  have hOGe : e (⟨(fr.ζ : G) * ω * (fr.ζ : G)⁻¹, hOGmem⟩ : Q)
      = SZ.torusAct ((fr.κ fr.ζ)⁻¹) (e ⟨ω, hωQ⟩) := by
    have h := heq (fr.ζ⁻¹ : fr.KW) (⟨ω, hωQ⟩ : Q)
      (⟨(fr.ζ : G) * ω * (fr.ζ : G)⁻¹, hOGmem⟩ : Q) (by
        show (fr.ζ : G) * ω * (fr.ζ : G)⁻¹ = (fr.ζ : G)⁻¹⁻¹ * ω * (fr.ζ : G)⁻¹
        rw [inv_inv])
    simpa using h
  have hLe : e (⟨(fr.ζ : G) * A * (fr.ζ : G)⁻¹ * fr.zc 1, hLmem⟩ : Q)
      = SZ.torusAct ((fr.κ fr.ζ)⁻¹) (e ⟨A, hAQ⟩) * (⟨0, 1, hone⟩ : SZ (E n)) := by
    rw [show (⟨(fr.ζ : G) * A * (fr.ζ : G)⁻¹ * fr.zc 1, hLmem⟩ : Q)
        = (⟨(fr.ζ : G) * A * (fr.ζ : G)⁻¹, hALmem⟩ : Q) * ssQ fr from by
      apply Subtype.ext; rw [Subgroup.coe_mul, ssQ_coe]]
    rw [map_mul, hssQe, hALe]
  have hRe : e (⟨(fr.ζ : G) ^ 2 * A * ((fr.ζ : G) ^ 2)⁻¹
        * ((fr.ζ : G) * ω * (fr.ζ : G)⁻¹), hRmem⟩ : Q)
      = SZ.torusAct (((fr.κ fr.ζ) ^ 2)⁻¹) (e ⟨A, hAQ⟩)
        * SZ.torusAct ((fr.κ fr.ζ)⁻¹) (e ⟨ω, hωQ⟩) := by
    rw [show (⟨(fr.ζ : G) ^ 2 * A * ((fr.ζ : G) ^ 2)⁻¹
          * ((fr.ζ : G) * ω * (fr.ζ : G)⁻¹), hRmem⟩ : Q)
        = (⟨(fr.ζ : G) ^ 2 * A * ((fr.ζ : G) ^ 2)⁻¹, hARmem⟩ : Q)
          * (⟨(fr.ζ : G) * ω * (fr.ζ : G)⁻¹, hOGmem⟩ : Q) from by
      apply Subtype.ext; rw [Subgroup.coe_mul]]
    rw [map_mul, hARe, hOGe]
  have heLR : SZ.torusAct ((fr.κ fr.ζ)⁻¹) (e ⟨A, hAQ⟩) * (⟨0, 1, hone⟩ : SZ (E n))
      = SZ.torusAct (((fr.κ fr.ζ) ^ 2)⁻¹) (e ⟨A, hAQ⟩)
        * SZ.torusAct ((fr.κ fr.ζ)⁻¹) (e ⟨ω, hωQ⟩) := by
    rw [← hLe, ← hRe, hLR]
  -- ### extract the coordinates
  have hx1 := congrArg (fun z : SZ (E n) => z.x) heLR
  have hy1 := congrArg (fun z : SZ (E n) => z.y) heLR
  simp only [SZ.mul_x, SZ.mul_y, SZ.torusAct_x, SZ.torusAct_y, SZ.mk_x, SZ.mk_y,
    Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, hc'', map_zero, mul_zero, add_zero,
    zero_mul] at hx1 hy1
  -- simplify the `σE`-terms
  have hsa : σE c⁻¹ = c := hσcinv
  simp only [hsa] at hy1
  have hsb : σE ((c ^ 2)⁻¹) = c ^ 2 := hσsqinv
  simp only [hsb] at hy1
  rw [map_mul, hsa] at hy1
  simp only [inv_mul_cancel₀ hc0, one_mul, mul_one, one_mul] at hy1
  -- ### algebra
  have hcc2 : (c ^ 2)⁻¹ * c ^ 2 = 1 := inv_mul_cancel₀ (pow_ne_zero 2 hc0)
  have hterm : (c ^ 2)⁻¹ * (e ⟨A, hAQ⟩).x * (c * σE ((e ⟨ω, hωQ⟩).x))
      = c⁻¹ * (e ⟨A, hAQ⟩).x * σE ((e ⟨ω, hωQ⟩).x) := by
    field_simp [hc0]
  have hy2 : 1 = (e ⟨ω, hωQ⟩).y + c⁻¹ * (e ⟨A, hAQ⟩).x * σE ((e ⟨ω, hωQ⟩).x) := by
    have h := hy1
    rw [hcc2, one_mul, hterm] at h
    rw [add_assoc, add_left_cancel_iff] at h
    exact h
  have hx2 : c⁻¹ * (e ⟨A, hAQ⟩).x
      = (c ^ 2)⁻¹ * (e ⟨A, hAQ⟩).x + c⁻¹ * (e ⟨ω, hωQ⟩).x := hx1
  have hx3 : c * (e ⟨A, hAQ⟩).x = (e ⟨A, hAQ⟩).x + c * (e ⟨ω, hωQ⟩).x := by
    have h2 : c ^ 2 * (c⁻¹ * (e ⟨A, hAQ⟩).x)
        = c ^ 2 * ((c ^ 2)⁻¹ * (e ⟨A, hAQ⟩).x + c⁻¹ * (e ⟨ω, hωQ⟩).x) := by rw [hx2]
    rw [mul_add, ← mul_assoc, ← mul_assoc, ← mul_assoc] at h2
    have hcc : c ^ 2 * c⁻¹ = c := by rw [pow_two, mul_assoc, mul_inv_cancel₀ hc0, mul_one]
    have hcc2' : c ^ 2 * (c ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 hc0)
    rw [hcc, hcc2', one_mul] at h2
    exact h2
  have hx4 : (e ⟨A, hAQ⟩).x * (1 + c⁻¹) = (e ⟨ω, hωQ⟩).x := by
    have h1 : (e ⟨A, hAQ⟩).x = c⁻¹ * (e ⟨A, hAQ⟩).x + (e ⟨ω, hωQ⟩).x := by
      have h := congrArg (fun z => c⁻¹ * z) hx3
      rw [← mul_assoc, inv_mul_cancel₀ hc0, one_mul, mul_add, ← mul_assoc,
        inv_mul_cancel₀ hc0, one_mul] at h
      exact h
    have hstep : (e ⟨A, hAQ⟩).x + c⁻¹ * (e ⟨A, hAQ⟩).x
        = (c⁻¹ * (e ⟨A, hAQ⟩).x + (e ⟨ω, hωQ⟩).x) + c⁻¹ * (e ⟨A, hAQ⟩).x :=
      congrArg (fun z => z + c⁻¹ * (e ⟨A, hAQ⟩).x) h1
    calc (e ⟨A, hAQ⟩).x * (1 + c⁻¹) = (e ⟨A, hAQ⟩).x + c⁻¹ * (e ⟨A, hAQ⟩).x := by
          rw [mul_add, mul_one, mul_comm ((e ⟨A, hAQ⟩).x) c⁻¹]
      _ = (c⁻¹ * (e ⟨A, hAQ⟩).x + (e ⟨ω, hωQ⟩).x) + c⁻¹ * (e ⟨A, hAQ⟩).x := hstep
      _ = (e ⟨ω, hωQ⟩).x := by
        rw [add_assoc, add_comm ((e ⟨ω, hωQ⟩).x) (c⁻¹ * (e ⟨A, hAQ⟩).x), ← add_assoc,
          CharTwo.add_self_eq_zero, zero_add]
  have hne1 : (1 + c⁻¹) ≠ 0 := by
    intro h
    have h1 : c⁻¹ = 1 := by
      calc c⁻¹ = c⁻¹ + 0 := (add_zero c⁻¹).symm
        _ = c⁻¹ + (1 + c⁻¹) := by rw [h]
        _ = (c⁻¹ + c⁻¹) + 1 := by rw [add_comm (1 : E n) c⁻¹, ← add_assoc]
        _ = 0 + 1 := by rw [CharTwo.add_self_eq_zero]
        _ = 1 := zero_add _
    exact hcne1 (by rw [← inv_inv c, h1, inv_one])
  have hx5 : (e ⟨A, hAQ⟩).x = (e ⟨ω, hωQ⟩).x * (1 + c⁻¹)⁻¹ := by
    calc (e ⟨A, hAQ⟩).x
        = ((e ⟨A, hAQ⟩).x * (1 + c⁻¹)) * (1 + c⁻¹)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hne1, mul_one]
      _ = (e ⟨ω, hωQ⟩).x * (1 + c⁻¹)⁻¹ := by rw [hx4]
  have hy4 : (e ⟨ω, hωQ⟩).y = 1 + c⁻¹ * (e ⟨A, hAQ⟩).x * σE ((e ⟨ω, hωQ⟩).x) := by
    have h : (e ⟨ω, hωQ⟩).y + c⁻¹ * (e ⟨A, hAQ⟩).x * σE ((e ⟨ω, hωQ⟩).x) = 1 := hy2.symm
    rw [← h, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hcadd : c + 1 ≠ 0 := by
    intro h
    have h1 : c = 1 := by
      calc c = c + 0 := (add_zero c).symm
        _ = c + (c + 1) := by rw [← h]
        _ = (c + c) + 1 := by rw [← add_assoc]
        _ = 0 + 1 := by rw [CharTwo.add_self_eq_zero]
        _ = 1 := zero_add _
    exact hcne1 h1
  have h5 : c⁻¹ * (1 + c⁻¹)⁻¹ = (c + 1)⁻¹ := by field_simp [hc0, hne1, hcadd]
  have h6 : (c + c⁻¹) * (c + 1)⁻¹ = 1 + c⁻¹ := by
    field_simp [hc0, hne1, hcadd]
    rw [CharTwo.add_sq, one_pow]
  rw [hy4, hx5]
  rw [show c⁻¹ * ((e ⟨ω, hωQ⟩).x * (1 + c⁻¹)⁻¹) * σE ((e ⟨ω, hωQ⟩).x)
      = ((e ⟨ω, hωQ⟩).x * σE ((e ⟨ω, hωQ⟩).x)) * (c⁻¹ * (1 + c⁻¹)⁻¹) from by ring]
  rw [hx0σ, h5, h6, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem omega_y_coord {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) {n : ℕ} (fr : Work.PSU3.CoarseFrame H Q t n) {ω : G}
    (hω : Work.PSU3.OmegaHyp fr ω)
    (hsq : ∀ a : (Work.PSU3.E n)ˣ, σE (a : Work.PSU3.E n) = a →
      (fr.nm a : Work.PSU3.E n) = (a : Work.PSU3.E n) ^ 2)
    (hω2 : ω ^ 2 = fr.zc ((fr.κ fr.ζ : Work.PSU3.E n) + (fr.κ fr.ζ : Work.PSU3.E n)⁻¹))
    (e : Q ≃* SZ (Work.PSU3.E n)) (μ : (Work.PSU3.E n)ˣ)
    (hex : ∀ x : Q, (e x).x = (μ : Work.PSU3.E n) * Multiplicative.toAdd (fr.bar x))
    (hes : ∀ hs : fr.zc 1 ∈ Q, (e ⟨fr.zc 1, hs⟩).x = 0 ∧ (e ⟨fr.zc 1, hs⟩).y = 1)
    (heq : ∀ (d : fr.KW) (x y : Q), (y : G) = (d : G)⁻¹ * x * d →
      e y = SZ.torusAct (fr.κ d) (e x)) :
    (e ⟨ω, hω.1⟩).y = (((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n))⁻¹ := by
  obtain ⟨hωQ, hω0, g, hgQ, hh, hhW, hrel⟩ := hω
  have hsplit : IsSplitRankOne H Q t := hS.split
  have hhζ : hh = (fr.ζ : G) ^ 3 := omega_h_eq hsplit fr hωQ hω0 hgQ hhW hrel
  have hrel_la : t * ω * t = g * hh * t * ((fr.ζ : G)⁻¹ * ω⁻¹) * (fr.ζ : G) := by
    rw [hrel]; group
  obtain ⟨A, hAQ, hAid⟩ := omega_s_identity hsplit fr hωQ hω0 hgQ hhW hhζ hrel_la
  exact omega_y_coord_aux hS fr hωQ hsq hω2 e μ hex hes heq hAQ hAid

end Work.PSU3.StageC
