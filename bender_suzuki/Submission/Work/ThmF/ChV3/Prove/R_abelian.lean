import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.ChV3.Prove.S1_centralizerP_eq
import Submission.Work.ThmF.ChV3.Prove.CG_pPart_101
import Submission.Work.ThmF.ChV3.Prove.card_sup_of_le_normalizer
import Submission.Work.ThmF.ChV3.Prove.S1_R_inf_CH_eq_P
import Submission.Work.ThmF.ChV3.Prove.Sig_sup_P_le_normalizer_CQ
import Submission.Work.ThmF.ChV3.Prove.card_eq_pPart_of_card_normalizer
import Submission.Work.ThmF.ChV3.Prove.R_abelian_transitivity
import Submission.Work.ThmF.ChV3.Prove.Sig_nontrivial_on_RP
import Submission.Work.ThmF.ChV3.Prove.ZRS_eq_P

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.R_abelian` — §3 leaf (11a): `R` is abelian

Peterfalvi II Ch. V §3, step (11) (p. 251), the non-abelian branch:

> Suppose `R` non-abelian.  Then `[R,R] = Z(R) = P` since `C_Q(P)` is transitive on `F^*`.
> We have `N(R) ⊆ N(P)`, and in case **(10-1)** `R` is a Sylow `p`-subgroup of `N(P)`, hence of
> `G`; but `|R| = p^{m+1}`, contradicting (10).  In case **(10-2)**, `RC_W(P)` is a Sylow
> 3-subgroup of `N(P)`.  Since `Σ` acts non-trivially on `R/P ≅ F`, `Z(RC_W(P)) = Z(R) = P`, so
> `N(RC_W(P)) ⊆ N(P)` and `RC_W(P)` is a Sylow 3-subgroup of `G`.  But `|RC_W(P)| = 3^4`,
> contradicting (10).  So `R` is abelian.

The formalisation of this leaf is organised in four independent pieces:

* `card_eq_pPart_of_card_normalizer` — the generic Sylow criterion
  (`R ≤ G` a `p`-subgroup with `|R| = |N_G(R)|_p` is Sylow in `G`);
* `R_abelian_transitivity` — `C_Q(P)` is transitive on `(R/P)^#`, the "`C_Q(P)` transitive on
  `F^*`" of the source, obtained from the fixed-point-freeness clause `h15.hfpf` plus the count
  `|C_Q(P)| + 1 = |R/P|`;
* `Sig_nontrivial_on_RP` — `Σ = C_W(P)` acts faithfully on `R/P` (the source's "`Σ` acts
  non-trivially on `R/P`", which here is a *consequence* of `hfpf` and `h7`, via
  `Ker = D ⊓ C_G(C_Q(P)) ⊓ C_G(P) = P`);
* `ZRS_eq_P` — from faithfulness, `Z(RΣ) = P`, whence `N_G(RΣ) ≤ N_G(P) = C_G(P)`.

Both cases of step (10) are then refuted here; each uses the **key structural consequence** of the
chain (Phase I below): if `R` is not abelian then `Z(R) = P`, so that `R/P` is abelian and
`N_G(R) ≤ N_G(Z(R)) = N_G(P) = C_G(P)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint
open scoped Pointwise

namespace Work.ThmF.ChV3.Prove

open Work.ThmF

variable {G : Type} [Group G] [Finite G]

/-! ## 0. Auxiliary arithmetic -/

/-- `pPart p (p ^ k * n) = p ^ k` when `p ∤ n`. -/
theorem pPart_mul_of_not_dvd {p k n : ℕ} (hp : p.Prime) (h : ¬ p ∣ n) :
    pPart p (p ^ k * n) = p ^ k := by
  have hn : n ≠ 0 := fun h0 => h (h0 ▸ dvd_zero p)
  have hpk : p ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
  unfold pPart
  rw [Nat.factorization_mul hpk hn, Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
    Nat.Prime.factorization_self hp, Nat.factorization_eq_zero_of_not_dvd h]
  simp

/-! ## 5. Phase I: in the non-abelian branch `Z(R) = P` -/

/-- `P` centralises `R` (since `R ≤ C_G(P)`), so `P ≤ Z(R) = C_G(R) ⊓ R`. -/
theorem P_le_center {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (h15 : Chain15 H Q t s r P) (h7 : Ker H Q P t = P) :
    P ≤ Subgroup.centralizer (h15.R : Set G) ⊓ h15.R := by
  refine le_inf ?_ ?_
  · rw [Subgroup.le_centralizer_iff]
    exact h15.hRc
  · exact fun x hx => h15.hNR (by rw [h7]; exact hx)

/-- **Phase I.**  If `R` is non-abelian, then `Z(R) = P`. -/
theorem center_eq_P_of_not_comm {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : CtxF H Q t s r P) (h15 : Chain15 H Q t s r P) (h7 : Ker H Q P t = P)
    (hpf : Nat.card P = orderOf (s * t)) (hNA : ¬ IsMulCommutative ↥h15.R) :
    Subgroup.centralizer (h15.R : Set G) ⊓ h15.R = P := by
  classical
  set Z : Subgroup G := Subgroup.centralizer (h15.R : Set G) ⊓ h15.R with hZ
  have hPZ : P ≤ Z := P_le_center h15 h7
  -- every element of `C_Q(P)` normalises `Z`
  have hAN : CQ Q P ≤ Subgroup.normalizer (Z : Set G) := by
    have h1 : CQ Q P ≤ Subgroup.normalizer (h15.R : Set G) :=
      fun y hy => h15.hRn (Subgroup.mem_inf.mp hy).2
    have h2 : CQ Q P ≤ Subgroup.normalizer (Subgroup.centralizer (h15.R : Set G) : Set G) :=
      h1.trans normalizer_le_normalizer_centralizer
    have h3 : CQ Q P ≤ Subgroup.normalizer (Subgroup.centralizer (h15.R : Set G) : Set G) ⊓
        Subgroup.normalizer (h15.R : Set G) := le_inf h2 h1
    refine h3.trans ?_
    have h4 := inf_normalizer_le_normalizer_inf
      (A := Subgroup.centralizer (h15.R : Set G)) (B := h15.R)
    rw [hZ]
    exact h4
  refine le_antisymm ?_ hPZ
  intro z hz
  by_contra hzP
  have hkey : ∀ w ∈ h15.R, w ∈ Z := by
    intro w hw
    by_cases hwP : w ∈ P
    · exact hPZ hwP
    · obtain ⟨y, hyA, hyP⟩ := R_abelian_transitivity c h15 h7 hpf hz.2 hw hzP hwP
      have hyNz : y ∈ Subgroup.normalizer (Z : Set G) := hAN hyA
      have hyz : y * z * y⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hyNz z).mp hz
      have hw_eq : w = (y * z * y⁻¹ * w⁻¹)⁻¹ * (y * z * y⁻¹) := by group
      rw [hw_eq]
      exact Z.mul_mem (hPZ (P.inv_mem hyP)) hyz
  have hcomm : ∀ a b : ↥h15.R, a * b = b * a := fun a b => Subtype.ext (by
    have ha : (a : G) ∈ Subgroup.centralizer (h15.R : Set G) :=
      (Subgroup.mem_inf.mp (hkey a a.2)).1
    exact ((Subgroup.mem_centralizer_iff.mp ha) b b.2).symm)
  exact hNA ⟨⟨hcomm⟩⟩

/-! ## 6. Case (10-1) is impossible -/

/-- **Case (10-1).** -/
theorem false_of_case101 {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : CtxF H Q t s r P) (h15 : Chain15 H Q t s r P) (h7 : Ker H Q P t = P)
    (hpf : Nat.card P = orderOf (s * t))
    (hZR : Subgroup.centralizer (h15.R : Set G) ⊓ h15.R = P)
    (h101 : Case101 H t P h15.m) : False := by
  classical
  have hp : (Nat.card P).Prime := c.P_prime
  -- ## `N_G(R) = C_G(P)`
  have hNR : Subgroup.normalizer (h15.R : Set G) = CG P := by
    refine le_antisymm ?_ h15.hRn
    have h : Subgroup.normalizer (h15.R : Set G) ≤
        Subgroup.normalizer ((Subgroup.centralizer (h15.R : Set G) ⊓ h15.R : Subgroup G) : Set G) :=
      (le_inf normalizer_le_normalizer_centralizer le_rfl).trans inf_normalizer_le_normalizer_inf
    rw [hZR, h15.hNG] at h
    exact h
  -- ## `|R| = |P| ^ (m+1)`
  have hpow : Nat.card h15.R = Nat.card P ^ (h15.m + 1) := by
    rw [h15.hcardR, h7, ← hpf, pow_succ']
  -- ## `|R| = pPart |P| |N_G(R)|`
  have hsylow : Nat.card h15.R = pPart (Nat.card P)
      (Nat.card ↥(Subgroup.normalizer (h15.R : Set G))) := by
    rw [hNR, CG_pPart_101 (m := h15.m) hFT hC4 c hpf h15.hm h15.hcq h101, ← hpow]
  have hRpg : IsPGroup (Nat.card P) h15.R := IsPGroup.of_card hpow
  -- ## the Sylow criterion contradicts `h101`
  have hGp : Nat.card h15.R = pPart (Nat.card P) (Nat.card G) :=
    card_eq_pPart_of_card_normalizer hp hRpg hsylow
  have hcontra : Nat.card P ^ (h15.m + 1) = Nat.card P ^ (h15.m + 2) := by
    rw [← hpow, hGp]
    exact h101.2
  have hlt : Nat.card h15.R < Nat.card P ^ (h15.m + 2) := by
    rw [hpow]
    exact Nat.pow_lt_pow_right c.P_prime.one_lt (by omega)
  omega

/-! ## 7. Case (10-2) is impossible -/

/-- **Case (10-2).** -/
theorem false_of_case102 {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : CtxF H Q t s r P) (h15 : Chain15 H Q t s r P) (h7 : Ker H Q P t = P)
    (hpf : Nat.card P = orderOf (s * t))
    (hZR : Subgroup.centralizer (h15.R : Set G) ⊓ h15.R = P)
    (hp3 : Nat.card P = 3) (hs3 : Nat.card ↥(Sig H t P) = 3)
    (hA8 : Nat.card ↥(CQ Q P) = 8)
    (hW39 : Nat.card ↥(W H t) = 3 ∨ Nat.card ↥(W H t) = 9)
    (hG3 : pPart 3 (Nat.card G) = 3 ^ 4 * Nat.card ↥(W H t)) : False := by
  classical
  -- ## `Σ` is faithful on `R/P`, so `Z(RΣ) = P`
  have hSig := Sig_nontrivial_on_RP (H := H) (Q := Q) (t := t) (s := s) (r := r) c h15 h7
  have hZRS := ZRS_eq_P (H := H) (Q := Q) (t := t) (s := s) (r := r) c h15 h7 hpf hp3 hA8 hZR hSig
  -- ## `m = 2` and `|R| = 27`
  have hf3 : orderOf (s * t) = 3 := by rw [← hpf, hp3]
  have hm2 : h15.m = 2 := by
    have h : orderOf (s * t) ^ h15.m = 9 := by rw [← h15.hcq, hA8]
    have h2 : 3 ^ h15.m = 3 ^ 2 := by
      rw [← hf3, h, hf3]
      norm_num
    exact Nat.pow_right_injective (by norm_num) h2
  have hcardR : Nat.card h15.R = 27 := by
    rw [h15.hcardR, h7, hp3, hf3, hm2]
    norm_num
  -- ## `R ⊓ Σ = ⊥`, so `|R ⊔ Σ| = 81`
  have hSig_le_W : Sig H t P ≤ W H t := inf_le_left
  have hSig_le_D : Sig H t P ≤ twoPoint H t :=
    (hSig_le_W.trans (W_le_centD H t)).trans (centD_le_twoPoint t)
  have hSig_le_H : Sig H t P ≤ H := hSig_le_D.trans inf_le_left
  have hSig_le_C : Sig H t P ≤ CG P := inf_le_right
  have hRinfH : h15.R ⊓ H = P := by
    have h := S1_R_inf_CH_eq_P (H := H) (Q := Q) (t := t) (s := s) (r := r) c h15 h7 hpf
    have heq : h15.R ⊓ H = h15.R ⊓ (H ⊓ CG P) := le_antisymm
      (le_inf (fun x hx => hx.1) (le_inf (fun x hx => hx.2) (fun x hx => h15.hRc hx.1)))
      (le_inf (fun x hx => hx.1) (fun x hx => hx.2.1))
    rw [heq, h]
  have hSig_inf_P : Sig H t P ⊓ P = ⊥ := by
    refine le_bot_iff.mp ?_
    calc Sig H t P ⊓ P ≤ W H t ⊓ P := le_inf (inf_le_left.trans hSig_le_W) inf_le_right
      _ = ⊥ := h15.hWP
  have hRinfSig : h15.R ⊓ Sig H t P = ⊥ := by
    have h1 : h15.R ⊓ Sig H t P ≤ P := by
      calc h15.R ⊓ Sig H t P ≤ h15.R ⊓ H := le_inf inf_le_left (inf_le_right.trans hSig_le_H)
        _ = P := hRinfH
    exact le_bot_iff.mp (le_inf inf_le_right h1 |>.trans (le_of_eq hSig_inf_P))
  have hSig_normR : Sig H t P ≤ Subgroup.normalizer (h15.R : Set G) :=
    fun x hx => h15.hRn (hSig_le_C hx)
  have hcardRS : Nat.card ↥(h15.R ⊔ Sig H t P) = 81 := by
    have h : Nat.card h15.R * Nat.card ↥(Sig H t P) = 81 := by
      rw [hcardR, hs3]
    rwa [card_sup_of_le_normalizer hSig_normR hRinfSig]
  -- ## `N_G(RΣ) ≤ C_G(P)`
  have hNle : Subgroup.normalizer ((h15.R ⊔ Sig H t P : Subgroup G) : Set G) ≤ CG P := by
    have h : Subgroup.normalizer ((h15.R ⊔ Sig H t P : Subgroup G) : Set G) ≤
        Subgroup.normalizer
          ((Subgroup.centralizer ((h15.R ⊔ Sig H t P : Subgroup G) : Set G) ⊓
            (h15.R ⊔ Sig H t P) : Subgroup G) : Set G) :=
      (le_inf normalizer_le_normalizer_centralizer le_rfl).trans inf_normalizer_le_normalizer_inf
    rw [hZRS, h15.hNG] at h
    exact h
  -- ## `pPart 3 |N_G(RΣ)| = 81`
  have hCGcard : Nat.card ↥(CG P) = 648 := by
    obtain ⟨-, -, hc⟩ := S1_centralizerP_eq (H := H) (Q := Q) (t := t) (s := s) (r := r)
      hFT hC4 c h15 h7 hpf
    rw [hc]
    have h : Nat.card h15.R * Nat.card ↥(CQ Q P) * Nat.card ↥(Sig H t P) = 648 := by
      rw [hcardR, hA8, hs3]
    exact h
  have hdvd_sup : Nat.card ↥(h15.R ⊔ Sig H t P) ∣
      Nat.card ↥(Subgroup.normalizer ((h15.R ⊔ Sig H t P : Subgroup G) : Set G)) :=
    Subgroup.card_dvd_of_le (H := h15.R ⊔ Sig H t P)
      (K := Subgroup.normalizer ((h15.R ⊔ Sig H t P : Subgroup G) : Set G))
      Subgroup.le_normalizer
  obtain ⟨d, hd⟩ : ∃ d, Nat.card ↥(Subgroup.normalizer
      ((h15.R ⊔ Sig H t P : Subgroup G) : Set G)) = Nat.card ↥(h15.R ⊔ Sig H t P) * d := hdvd_sup
  rw [hcardRS] at hd
  have hdvd8 : d ∣ 8 := by
    have h1 : Nat.card ↥(Subgroup.normalizer ((h15.R ⊔ Sig H t P : Subgroup G) : Set G)) ∣
        Nat.card ↥(CG P) := Subgroup.card_dvd_of_le hNle
    rw [hCGcard, hd] at h1
    norm_num at h1
    exact (Nat.mul_dvd_mul_iff_left (show 0 < (81 : ℕ) by norm_num)).mp h1
  have h3d : ¬ 3 ∣ d := by
    intro h
    have h38 : (3 : ℕ) ∣ 8 := h.trans hdvd8
    norm_num at h38
  have hppart : pPart 3 (Nat.card ↥(Subgroup.normalizer
      ((h15.R ⊔ Sig H t P : Subgroup G) : Set G))) = 81 := by
    rw [hd, show (81 : ℕ) = 3 ^ 4 by norm_num]
    exact pPart_mul_of_not_dvd (p := 3) (k := 4) (n := d) (by norm_num) h3d
  -- ## the Sylow criterion, against `hG3`
  have hpg : IsPGroup 3 ↥(h15.R ⊔ Sig H t P) :=
    IsPGroup.of_card (n := 4) (by rw [hcardRS]; norm_num)
  have hGp : Nat.card ↥(h15.R ⊔ Sig H t P) = pPart 3 (Nat.card G) :=
    card_eq_pPart_of_card_normalizer (p := 3) (by norm_num) hpg (by rw [hppart, hcardRS])
  rw [hG3, hcardRS] at hGp
  rcases hW39 with h3 | h9
  · rw [h3] at hGp; norm_num at hGp
  · rw [h9] at hGp; norm_num at hGp

/-! ## 8. The leaf -/

theorem R_abelian {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (h7 : Work.ThmF.ChV3.Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    (h10 : Work.ThmF.ChV3.Case101 H t P h15.m ∨
      (Nat.card P = 3 ∧ Nat.card ↥(Work.ThmF.ChV3.Sig H t P) = 3 ∧
        Nat.card ↥(Work.ThmF.ChV3.CQ Q P) = 8 ∧
        (Nat.card ↥(Work.ThmF.W H t) = 3 ∨ Nat.card ↥(Work.ThmF.W H t) = 9) ∧
        Work.ThmF.ChV3.pPart 3 (Nat.card G) = 3 ^ 4 * Nat.card ↥(Work.ThmF.W H t))) :
    IsMulCommutative ↥h15.R := by
  classical
  by_contra hNA
  have hZR := center_eq_P_of_not_comm (H := H) (Q := Q) (t := t) (s := s) (r := r) c h15 h7 hpf hNA
  rcases h10 with h101 | ⟨hp3, hs3, hA8, hW39, hG3⟩
  · exact false_of_case101 (H := H) (Q := Q) (t := t) (s := s) (r := r)
      hFT hC4 c h15 h7 hpf hZR h101
  · exact false_of_case102 (H := H) (Q := Q) (t := t) (s := s) (r := r)
      hFT hC4 c h15 h7 hpf hZR hp3 hs3 hA8 hW39 hG3

end Work.ThmF.ChV3.Prove
