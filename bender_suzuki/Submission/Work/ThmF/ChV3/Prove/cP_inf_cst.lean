import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Prove.Step9Defs
-- NB: `cst_isPGroup` (step (13), still a `sorry` stub) is **not** needed: the
-- fixed-point-freeness clause `Chain15.hfpf` of step (2) gives `C_{C_Q(P)}(st) = 1`
-- directly, which (with `R` abelian, `st ∈ R`) computes `C_G(P) ⊓ C_G(st) = R Σ`.
import Submission.Work.ThmF.ChV3.Prove.S1_centralizerP_eq
import Submission.Work.ThmF.ChV3.Prove.S2_commS_mem_R
import Submission.Work.ThmF.ChV3.Prove.card_sup_of_le_normalizer
import Submission.Work.ThmF.Prove.centDLowerCentralizerS

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.cP_inf_cst` — §3 leaf 14b: `C_{C_G(P)}(st) = R Σ`

Peterfalvi II Ch. V §3, step (14), first half: in case (10-2),

  `C_G(P) ⊓ C_G(st) = R Σ`,   of order `81 = 27 · 3`.

The proof here does **not** need step (13) (`C_G(st)` is a 3-group); it is an element chase
inside `C_G(P)`, whose structure is S1 (`S1_centralizerP_eq`, proved):

* `C_G(P) = R · (C_Q(P) ⊔ Σ)` with `R ⊓ (C_Q(P) ⊔ Σ) = ⊥` (`R` normal in `C_G(P)`);
* `Σ ≤ V = C_D(t) ≤ C_G(s)` (Ch. V §2 Lemma 3 a), so `Σ` centralises `st`; `Σ ≤ H`, so `Σ`
  normalises `C_Q(P)` and `C_Q(P) ⊔ Σ = C_Q(P) · Σ`;
* `R` is abelian (`Step11Out.comm`) and contains `st`: `[st, s] = (st)² ∈ R` by S2
  (`S2_commS_mem_R`), and `st = ((st)²)⁻¹` because `o(st) = 3`; moreover `st ∉ Ker = P`
  (else `t = s · st ∈ H`).

So for `x = r·m` (`r ∈ R`, `m ∈ C_Q(P) ⊔ Σ`) with `x st x⁻¹ = st`, writing `m = c·σ` gives
`st = m st m⁻¹ = c st c⁻¹`, i.e. `[c, st] = 1`, and the fixed-point-freeness clause `hfpf` of
step (2) (applied at `x = st ∉ Ker`) forces `c = 1`. Hence `x ∈ R ⊔ Σ`.

The numerical part uses `|R| = |Ker| · o(st)^m = 3 · 3² = 27` (`h7`, `hpf`, `d.f3`, and `m = 2`
from `|C_Q(P)| + 1 = o(st)^m = 9`) and `|Σ| = 3` (`d.sig3`), so `|R ⊔ Σ| = 27 · 3 = 81`.
-/

set_option linter.unusedVariables false

open Classical LeanEval.GroupTheory.Defs

open scoped Pointwise

namespace Work.ThmF.ChV3.Prove

variable {G : Type} [Group G] [Finite G]

/-- `IsMulCommutative`, in elementwise form. -/
private lemma comm_of_isMulCommutative' {R : Subgroup G} (h : IsMulCommutative ↥R) :
    ∀ x ∈ R, ∀ y ∈ R, x * y = y * x :=
  fun x hx y hy => congrArg Subtype.val (h.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

/-- An element commuting with `s` and with `t` commutes with `s * t`. -/
private lemma comm_mul_st {s t x : G} (hs : x * s = s * x) (ht : x * t = t * x) :
    x * (s * t) = (s * t) * x := by
  calc x * (s * t) = (x * s) * t := by rw [mul_assoc]
    _ = (s * x) * t := by rw [hs]
    _ = s * (x * t) := by rw [mul_assoc]
    _ = s * (t * x) := by rw [ht]
    _ = (s * t) * x := by rw [mul_assoc]

/-- `Σ = C_W(P) ≤ V = C_D(t) ≤ C_G(s) ⊓ C_G(t) ≤ C_G(st)`. -/
private lemma sig_le_cst {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) :
    Work.ThmF.ChV3.Sig H t P ≤ Work.ThmF.ChV3.Cst s t := by
  intro σ hσ
  have hσV : σ ∈ Submission.Blueprint.centD H t :=
    Work.ThmF.W_le_centD H t (Subgroup.mem_inf.mp hσ).1
  have hσs : σ * s = s * σ :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (Work.ThmF.Prove.centDLowerCentralizerS c.split c.s_mem c.s_inv c.r_mem c.sid hσV)
  have hσt : σ * t = t * σ :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hσV).2
  exact Subgroup.mem_centralizer_singleton_iff.mpr (comm_mul_st hσs hσt)

theorem cP_inf_cst {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (h7 : Work.ThmF.ChV3.Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    {T : Subgroup G} (h11 : Work.ThmF.ChV3.Step11Out H Q t P h15.R T)
    (d : Work.ThmF.ChV3.Case102 H Q t s P) :
    Work.ThmF.ChV3.CG P ⊓ Work.ThmF.ChV3.Cst s t =
        h15.R ⊔ Work.ThmF.ChV3.Sig H t P ∧
      Nat.card ↥(h15.R ⊔ Work.ThmF.ChV3.Sig H t P) = 81 := by
  classical
  -- ## S1: `C_G(P) = R · (C_Q(P) ⊔ Σ)`, with trivial intersection
  obtain ⟨hRinfM, hRsupM, -⟩ := S1_centralizerP_eq hFT hC4 c h15 h7 hpf
  -- ## Containments
  have hMleCG : Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P ≤ Work.ThmF.ChV3.CG P :=
    hRsupM ▸ (le_sup_right : Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P ≤
      h15.R ⊔ (Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P))
  have hMnormR : Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P ≤
      Subgroup.normalizer (h15.R : Set G) := hMleCG.trans h15.hRn
  have hSigCG : Work.ThmF.ChV3.Sig H t P ≤ Work.ThmF.ChV3.CG P :=
    fun σ hσ => hMleCG (Subgroup.mem_sup_right hσ)
  have hSigNormR : Work.ThmF.ChV3.Sig H t P ≤ Subgroup.normalizer (h15.R : Set G) :=
    fun σ hσ => hMnormR (Subgroup.mem_sup_right hσ)
  have hSigCst : Work.ThmF.ChV3.Sig H t P ≤ Work.ThmF.ChV3.Cst s t := sig_le_cst c
  have hRcomm : ∀ x ∈ h15.R, ∀ y ∈ h15.R, x * y = y * x :=
    comm_of_isMulCommutative' h11.comm
  -- ## `s² = t² = 1`
  have hs2 : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rwa [c.s_inv, pow_two] at h
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [c.split.invol, pow_two] at h
  -- ## `st ∈ C_G(P)`
  have hstCG : s * t ∈ Work.ThmF.ChV3.CG P := by
    rw [Work.ThmF.ChV3.CG, Subgroup.mem_centralizer_iff]
    intro x hx
    have hxV : x ∈ Submission.Blueprint.centD H t := c.P_le hx
    have hxs : x * s = s * x :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (Work.ThmF.Prove.centDLowerCentralizerS c.split c.s_mem c.s_inv c.r_mem c.sid hxV)
    have hxt : x * t = t * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hxV).2
    exact comm_mul_st hxs hxt
  -- ## `st ∈ R`: S2 turns the commutator `[st, s]` into `(st)²`
  have hst3 : (s * t) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (s * t)
    rwa [d.f3] at h
  have hst2inv : (s * t) ^ 2 = (s * t)⁻¹ := by
    have h : (s * t) ^ 2 * (s * t) = 1 := by
      rw [← pow_succ, hst3]
    exact eq_inv_of_mul_eq_one_left h
  have hstR : s * t ∈ h15.R := by
    have hmem : (s * t) * s * (s * t)⁻¹ * s⁻¹ ∈ h15.R :=
      S2_commS_mem_R hFT hC4 c hpf hRsupM h15.hRn (s * t) hstCG
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have heq : (s * t) * s * (s * t)⁻¹ * s⁻¹ = (s * t)⁻¹ := by
      have h1 : (s * t) * s * (s * t)⁻¹ * s⁻¹ = (s * t) * (s * t) := by
        rw [mul_inv_rev, hsinv, htinv]
        rw [show (s * t) * s * (t * s) * s = (s * t) * ((s * t) * (s * s)) by group]
        rw [hs2, mul_one]
      rw [h1]
      simpa [pow_two] using hst2inv
    rw [heq] at hmem
    simpa using h15.R.inv_mem hmem
  -- ## `st ∉ Ker = P`
  have hstNotKer : s * t ∉ Work.ThmF.ChV3.Ker H Q P t := by
    intro hmem
    rw [h7] at hmem
    have hstH : s * t ∈ H := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (c.P_le hmem)).1).1
    have ht_eq : t = s * (s * t) := by rw [← mul_assoc, hs2, one_mul]
    exact c.split.not_mem (ht_eq ▸ H.mul_mem (c.split.le c.s_mem) hstH)
  -- ## `Σ` normalises `C_Q(P)`
  have hSigNormCQ : Work.ThmF.ChV3.Sig H t P ≤
      Subgroup.normalizer (Work.ThmF.ChV3.CQ Q P : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro σ hσ cc hcc
    obtain ⟨hcQ, hcP⟩ := Subgroup.mem_inf.mp hcc
    have hσW : σ ∈ Work.ThmF.W H t := (Subgroup.mem_inf.mp hσ).1
    have hσP : σ ∈ Subgroup.centralizer (P : Set G) := (Subgroup.mem_inf.mp hσ).2
    have hσH : σ ∈ H :=
      (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (Work.ThmF.W_le_centD H t hσW)).1).1
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (c.split.normal hσH) cc).mp hcQ
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hσy : y * σ = σ * y := Subgroup.mem_centralizer_iff.mp hσP y hy
      have hcy : y * cc = cc * y := Subgroup.mem_centralizer_iff.mp hcP y hy
      have hσy' : y * σ⁻¹ = σ⁻¹ * y :=
        Subgroup.mem_centralizer_iff.mp ((Subgroup.centralizer (P : Set G)).inv_mem hσP) y hy
      calc y * (σ * cc * σ⁻¹) = (y * σ) * (cc * σ⁻¹) := by group
        _ = (σ * y) * (cc * σ⁻¹) := by rw [hσy]
        _ = σ * (y * cc) * σ⁻¹ := by group
        _ = σ * (cc * y) * σ⁻¹ := by rw [hcy]
        _ = (σ * cc) * (y * σ⁻¹) := by group
        _ = (σ * cc) * (σ⁻¹ * y) := by rw [hσy']
        _ = (σ * cc * σ⁻¹) * y := by group
  -- ## The element chase
  have hle : Work.ThmF.ChV3.CG P ⊓ Work.ThmF.ChV3.Cst s t ≤
      h15.R ⊔ Work.ThmF.ChV3.Sig H t P := by
    intro x hx
    obtain ⟨hxCP, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxC' : x * (s * t) = (s * t) * x :=
      Subgroup.mem_centralizer_singleton_iff.mp hxC
    -- write `x = r * m` with `r ∈ R`, `m ∈ C_Q(P) ⊔ Σ`
    have hxRM : x ∈ h15.R ⊔ (Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P) := by
      rw [hRsupM]; exact hxCP
    have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left h15.R
      (Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P) hMnormR
    have hxM : x ∈ (h15.R : Set G) *
        ((Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P : Subgroup G) : Set G) := by
      rw [← hcoe]; exact hxRM
    rw [Set.mem_mul] at hxM
    obtain ⟨rr, hrr, mm, hmm, hrm⟩ := hxM
    rw [← hrm] at hxC' ⊢
    -- `m` commutes with `st` (as `r` does, `R` being abelian and containing `st`)
    have hrrC : rr * (s * t) = (s * t) * rr := hRcomm rr hrr (s * t) hstR
    have hmmC : mm * (s * t) = (s * t) * mm := by
      have h1 : rr * (mm * (s * t)) = rr * ((s * t) * mm) := by
        calc rr * (mm * (s * t)) = (rr * mm) * (s * t) := by group
          _ = (s * t) * (rr * mm) := hxC'
          _ = ((s * t) * rr) * mm := by group
          _ = (rr * (s * t)) * mm := by rw [hrrC]
          _ = rr * ((s * t) * mm) := by group
      exact mul_left_cancel h1
    -- write `m = c * σ` with `c ∈ C_Q(P)`, `σ ∈ Σ`
    have hcoe2 := Subgroup.coe_mul_of_right_le_normalizer_left (Work.ThmF.ChV3.CQ Q P)
      (Work.ThmF.ChV3.Sig H t P) hSigNormCQ
    have hmm' : mm ∈ ((Work.ThmF.ChV3.CQ Q P : Subgroup G) : Set G) *
        ((Work.ThmF.ChV3.Sig H t P : Subgroup G) : Set G) := by
      rw [← hcoe2]; exact hmm
    rw [Set.mem_mul] at hmm'
    obtain ⟨cc, hcc, σ, hσ, hcσ⟩ := hmm'
    rw [← hcσ] at hmmC
    -- `σ` commutes with `st`
    have hσC : σ * (s * t) = (s * t) * σ :=
      Subgroup.mem_centralizer_singleton_iff.mp (hSigCst hσ)
    -- hence `c` commutes with `st`
    have hccC : cc * (s * t) = (s * t) * cc := by
      have h1 : (cc * (s * t)) * σ = ((s * t) * cc) * σ := by
        calc (cc * (s * t)) * σ = cc * ((s * t) * σ) := by group
          _ = cc * (σ * (s * t)) := by rw [← hσC]
          _ = (cc * σ) * (s * t) := by group
          _ = (s * t) * (cc * σ) := hmmC
          _ = ((s * t) * cc) * σ := by group
      exact mul_right_cancel h1
    -- fixed-point-freeness of `C_Q(P)` on `R ∖ Ker` forces `c = 1`
    have hcc1 : cc = 1 := by
      have hcomm1 : cc * (s * t) * cc⁻¹ * (s * t)⁻¹ = 1 := by rw [hccC]; group
      have hmemKer : cc * (s * t) * cc⁻¹ * (s * t)⁻¹ ∈ Work.ThmF.ChV3.Ker H Q P t := by
        rw [hcomm1]; exact (Work.ThmF.ChV3.Ker H Q P t).one_mem
      exact h15.hfpf (s * t) hstR hstNotKer cc hcc hmemKer
    have hmmσ : mm = σ := by rw [← hcσ, hcc1, one_mul]
    rw [hmmσ]
    exact Subgroup.mul_mem_sup hrr hσ
  -- ## The reverse inclusion
  have hge : h15.R ⊔ Work.ThmF.ChV3.Sig H t P ≤
      Work.ThmF.ChV3.CG P ⊓ Work.ThmF.ChV3.Cst s t :=
    sup_le (le_inf h15.hRc (fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hRcomm y hy (s * t) hstR)))
      (le_inf hSigCG hSigCst)
  -- ## `|R| = 27` and `|Σ| = 3`
  have hm2 : h15.m = 2 := by
    have h : 3 ^ h15.m = 9 := by
      have h := h15.hcq
      rw [d.cq8, d.f3] at h
      exact h.symm
    have h2 : 3 ^ h15.m = 3 ^ 2 := by rw [h]; norm_num
    exact Nat.pow_right_injective (show 2 ≤ 3 by norm_num) h2
  have hcardR : Nat.card ↥h15.R = 27 := by
    have h := h15.hcardR
    rw [h7, hpf, d.f3, hm2] at h
    rw [h]
    norm_num
  have hRinfSig : h15.R ⊓ Work.ThmF.ChV3.Sig H t P = ⊥ := by
    have hle : h15.R ⊓ Work.ThmF.ChV3.Sig H t P ≤
        h15.R ⊓ (Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P) :=
      le_inf inf_le_left (inf_le_right.trans le_sup_right)
    rw [hRinfM] at hle
    exact le_bot_iff.mp hle
  have hcard81 : Nat.card ↥(h15.R ⊔ Work.ThmF.ChV3.Sig H t P) = 81 := by
    rw [card_sup_of_le_normalizer hSigNormR hRinfSig, hcardR, d.sig3]
  exact ⟨le_antisymm hle hge, hcard81⟩

end Work.ThmF.ChV3.Prove
