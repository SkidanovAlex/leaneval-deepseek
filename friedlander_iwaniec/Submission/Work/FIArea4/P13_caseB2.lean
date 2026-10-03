import Mathlib
import Submission.Work.FIArea4.P13Defs
import Submission.Work.FIArea4.P13Scale
import Submission.Work.FIArea4.P13basic

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 8000000

noncomputable section

/-! ## Nonnegativity of the ingredients of the local variance -/

lemma P13b2_Evar_nonneg (R S d : ℕ) (α : ℕ → ℕ → ℂ) :
    0 ≤ Work.FIPlan.Evar R S d α := by
  rw [Work.FIPlan.Evar]
  exact Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _)

lemma P13b2_EvarA_nonneg (R S d p : ℕ) (α : ℕ → ℕ → ℂ) :
    0 ≤ EvarA R S d p α := by
  rw [EvarA]
  exact Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _)

lemma P13b2_EvarB_nonneg (R S d p : ℕ) (α : ℕ → ℕ → ℂ) :
    0 ≤ EvarB R S d p α := by
  rw [EvarB]
  exact Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _)

lemma P13b2_Vvar_nonneg (R S D : ℕ) (α : ℕ → ℕ → ℂ) :
    0 ≤ Work.FIPlan.Vvar R S D α := by
  rw [Work.FIPlan.Vvar]
  exact Finset.sum_nonneg (fun d _ => P13b2_Evar_nonneg R S d α)

lemma P13b2_L2p_nonneg (R S p : ℕ) (α : ℕ → ℕ → ℂ) : 0 ≤ L2p R S p α := by
  rw [L2p]
  exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _))

lemma P13b2_p14L2_nonneg (R S : ℕ) (α : ℕ → ℕ → ℂ) : 0 ≤ p14L2 R S α := by
  rw [p14L2]
  exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _))

lemma P13b2_p14Ener_nonneg (R S : ℕ) (α : ℕ → ℕ → ℂ) : 0 ≤ p14Ener R S α := by
  rw [p14Ener]
  exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ =>
    mul_nonneg (by positivity) (Complex.normSq_nonneg _)))

/-! ## The dyadic decomposition `(a,8a] = (a,2a] ⊔ (2a,4a] ⊔ (4a,8a]` -/

lemma P13b2_dyadic (a : ℕ) :
    Finset.Ioc a (2*(2*(2*a)))
      = Finset.Ioc a (2 * a) ∪ Finset.Ioc (2 * a) (2*(2*a)) ∪ Finset.Ioc (2*(2*a)) (2*(2*(2*a))) := by
  have e1 : Finset.Ioc a (2 * a) ∪ Finset.Ioc (2 * a) (2*(2*a)) = Finset.Ioc a (2*(2*a)) :=
    Finset.Ioc_union_Ioc_eq_Ioc (by omega) (by omega)
  have e2 : Finset.Ioc a (2*(2*a)) ∪ Finset.Ioc (2*(2*a)) (2*(2*(2*a))) = Finset.Ioc a (2*(2*(2*a))) :=
    Finset.Ioc_union_Ioc_eq_Ioc (by omega) (by omega)
  rw [← e2, ← e1]

lemma P13b2_sum_dyadic (a : ℕ) (f : ℕ → ℝ) :
    ∑ e ∈ Finset.Ioc a (2*(2*(2*a))), f e
      = ∑ e ∈ Finset.Ioc a (2 * a), f e + ∑ e ∈ Finset.Ioc (2 * a) (2*(2*a)), f e
        + ∑ e ∈ Finset.Ioc (2*(2*a)) (2*(2*(2*a))), f e := by
  rw [P13b2_dyadic a]
  have hd1 : Disjoint (Finset.Ioc a (2 * a)) (Finset.Ioc (2 * a) (2*(2*a))) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    rw [Finset.mem_Ioc] at hx1 hx2; omega
  have hd2 : Disjoint (Finset.Ioc a (2 * a) ∪ Finset.Ioc (2 * a) (2*(2*a)))
      (Finset.Ioc (2*(2*a)) (2*(2*(2*a)))) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    rw [Finset.mem_union] at hx1
    rw [Finset.mem_Ioc] at hx2
    rcases hx1 with h | h
    · rw [Finset.mem_Ioc] at h; omega
    · rw [Finset.mem_Ioc] at h; omega
  rw [Finset.sum_union hd2, Finset.sum_union hd1]

/-- For `x ≥ 1` and `ε > 0`, `log x ≤ (8/ε) x^{ε/8}`. -/
private lemma P13b2_log_le_const_mul_rpow {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ (8/ε) * x^(ε/8) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hu0 : 0 < x^(ε/8) := Real.rpow_pos_of_pos hx0 _
  have h1 : Real.log (x^(ε/8)) ≤ x^(ε/8) := by
    have := Real.log_le_sub_one_of_pos hu0
    linarith
  have h2 : Real.log (x^(ε/8)) = (ε/8) * Real.log x := Real.log_rpow hx0 (ε/8)
  have h3 : (8/ε) * ((ε/8) * Real.log x) = Real.log x := by field_simp
  calc Real.log x = (8/ε) * ((ε/8) * Real.log x) := h3.symm
    _ = (8/ε) * Real.log (x^(ε/8)) := by rw [h2]
    _ ≤ (8/ε) * x^(ε/8) := by
        apply mul_le_mul_of_nonneg_left h1
        positivity

/-! ## The main theorem -/

theorem P13_caseB2 (ε : ℝ) (hε : 0 < ε) (C121 : ℝ) (hC121 : 0 < C121)
    (h121 : ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
        (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
        Work.FIPlan.Vvar R S D α ≤ C121 * p14T12 D R S (ε / 8) * p14Ener R S α)
    (KE : ℝ) (hKE : 0 < KE)
    (hEner : ∀ (R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ R → 1 ≤ S →
        p14Ener R S α ≤ KE * (((R:ℝ)*(S:ℝ))^(ε/4)) * p14L2 R S α)
    (Kns : ℝ) (hKns : 0 < Kns)
    (hns : ∀ (D R S : ℕ) (P : ℝ) (D' : ℕ), 1 ≤ D → 1 ≤ R → 1 ≤ S → P = p13P D R S → 1 < P →
        1 ≤ D' → (D:ℝ) * P^2 / 2 ≤ (D':ℝ) → (D':ℝ) ≤ 16 * (D:ℝ) * P^2 →
        P * p14T12 D' R S (ε/8) ≤ Kns * p14T13 D R S ε * (((R:ℝ) * (S:ℝ)) ^ (ε/2)))
    (cp : ℝ) (hcp : 0 < cp)
    (hpc : ∀ n : ℕ, 2 ≤ n →
        cp * (n : ℝ) / Real.log (2 * (n:ℝ)) ≤ (((Finset.Ioc n (2*n)).filter Nat.Prime).card : ℝ))
    (Kpd : ℝ) (hKpd : 0 < Kpd)
    (hpd : ∀ (R S N r : ℕ), 1 ≤ R → 1 ≤ S → 1 ≤ r → r ≤ 2 * R →
        ((((Finset.Ioc N (2 * N)).filter Nat.Prime).filter (fun p => p ∣ r)).card : ℝ)
          ≤ Kpd * (((R : ℝ) * (S : ℝ)) ^ (ε/8)))
    (hL2p : ∀ (R S : ℕ) (α : ℕ → ℕ → ℂ) (W : Finset ℕ) (K : ℝ), 0 ≤ K →
        (∀ r : ℕ, 1 ≤ r → r ≤ 2 * R → ((W.filter (fun p => p ∣ r)).card : ℝ) ≤ K) →
        ∑ p ∈ W, L2p R S p α ≤ K * p14L2 R S α)
    (Kaf : ℝ) (hKaf : 0 < Kaf)
    (haf : ∀ (D R S : ℕ), 1 ≤ D → 1 ≤ R → 1 ≤ S → 1 < p13P D R S →
        (D:ℝ) / p13P D R S ≤ p14T13 D R S ε ∧
        1 / p13P D R S ≤ p14T13 D R S ε ∧
        ((R:ℝ)*(S:ℝ)) / (p13P D R S)^2 ≤ p14T13 D R S ε ∧
        Real.log (4 * p13P D R S) ≤ Kaf * (((R:ℝ)*(S:ℝ))^(ε/8)) ∧
        (∀ x : ℝ, 1 ≤ x → x ≤ 32 * (((R:ℝ)*(S:ℝ))^(3/4)) →
            Real.log x ≤ Kaf * (((R:ℝ)*(S:ℝ))^(ε/8))))
    (Kt : ℝ) (hKt : 0 < Kt)
    (htau : ∀ n : ℕ, 1 ≤ n → ((n.divisors.card : ℕ) : ℝ) ≤ Kt * (n : ℝ) ^ (ε / 4))
    (heb : ∀ (D R S p : ℕ) (α : ℕ → ℕ → ℂ) (B : ℝ), 1 ≤ p →
        (∀ m : ℕ, 1 ≤ m → m ≤ 8*R*S → ((m.divisors.card : ℕ):ℝ) ≤ B) →
        (∀ r s, α r s ≠ 0 → Nat.Coprime r (2*s)) →
        ∑ d ∈ Finset.Ioc D (2*D), EvarB R S d p α ≤
          ((D:ℝ) + B * (4*(R:ℝ)*(S:ℝ)/(p:ℝ) + 4)) * L2p R S p α)
    (hea : ∀ (R S d p : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ d → p.Prime →
        EvarA R S d p α ≤ (p:ℝ)^2 * Work.FIPlan.Evar R S (d * p^2) α)
    (hm : ∀ (D R S : ℕ) (W : Finset ℕ) (α : ℕ → ℕ → ℂ) (e₁ e₂ : ℕ), 1 ≤ e₁ →
        (∀ p ∈ W, Nat.Prime p) →
        (∀ p ∈ W, ∀ d ∈ Finset.Ioc D (2 * D), e₁ < d * p ^ 2) →
        (∀ p ∈ W, ∀ d ∈ Finset.Ioc D (2 * D), d * p ^ 2 ≤ e₂) →
        ∑ p ∈ W, ∑ d ∈ Finset.Ioc D (2 * D), Work.FIPlan.Evar R S (d * p ^ 2) α
          ≤ (Real.log (e₂:ℝ)/Real.log 4 + 2) * ∑ e ∈ Finset.Ioc e₁ e₂, Work.FIPlan.Evar R S e α)
    : ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
        (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) → 1 < p13P D R S →
        Work.FIPlan.Vvar R S D α ≤ C * p14T13 D R S ε * (((R:ℝ)*(S:ℝ))^ε) * p14L2 R S α := by
  refine ⟨96 * C121 * Kns * KE * Kaf * ((Real.log 32 + (3:ℝ)/4 * (8/ε))/Real.log 4 + 2) / cp
      + (2 * Kaf * Kpd / cp) * (1 + 8 * Kt * (8:ℝ)^(ε/4)),
    ?_, ?_⟩
  · positivity
  · intro D R S α hD hR hS hsup hPgt1
    have h8pow : (0:ℝ) < (8:ℝ)^(ε/4) := Real.rpow_pos_of_pos (by norm_num) _
    have hDpos : (0:ℝ) < (D:ℝ) := by exact_mod_cast (by omega : 0 < D)
    set X : ℝ := (R:ℝ)*(S:ℝ) with hX
    have hR1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
    have hS1 : (1:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
    have hX1 : 1 ≤ X := by rw [hX]; nlinarith
    have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX1
    set P : ℝ := p13P D R S with hP
    have hPpos : 0 < P := by rw [hP]; exact p13P_pos D R S hD hR hS
    have hP1 : 1 < P := hPgt1
    set Kaf2 : ℝ := (Real.log 32 + (3:ℝ)/4 * (8/ε))/Real.log 4 + 2 with hKaf2
    set Nn : ℕ := ⌈P⌉₊ with hNn
    have hNn_ge : P ≤ (Nn:ℝ) := by rw [hNn]; exact Nat.le_ceil P
    have hNn_lt : (Nn:ℝ) < P + 1 := by rw [hNn]; exact Nat.ceil_lt_add_one hPpos.le
    have hNn_le : (Nn:ℝ) ≤ 2*P := by linarith
    have hNn2 : 2 ≤ Nn := by
      have h : (1:ℕ) < Nn := by
        have : (1:ℝ) < (Nn:ℝ) := lt_of_lt_of_le hP1 hNn_ge
        exact_mod_cast this
      omega
    have hNn1 : 1 ≤ Nn := by omega
    have hNnpos : (0:ℝ) < (Nn:ℝ) := by exact_mod_cast (by omega : 0 < Nn)
    set W : Finset ℕ := (Finset.Ioc Nn (2*Nn)).filter Nat.Prime with hW
    have hWprime : ∀ p ∈ W, Nat.Prime p := by
      intro p hp; rw [hW] at hp; exact (Finset.mem_filter.mp hp).2
    have hWmem : ∀ p, p ∈ W ↔ (Nn < p ∧ p ≤ 2*Nn ∧ Nat.Prime p) := by
      intro p; rw [hW]; simp only [Finset.mem_filter, Finset.mem_Ioc]; tauto
    have hlog4P : 0 < Real.log (4*P) := by apply Real.log_pos; linarith
    have hWcard : cp * P / Real.log (4*P) ≤ (W.card:ℝ) := by
      have h1 := hpc Nn hNn2
      have hlog1 : 0 < Real.log (2*(Nn:ℝ)) := by
        apply Real.log_pos
        have : (2:ℝ) ≤ 2*(Nn:ℝ) := by linarith
        linarith
      have hlog2 : Real.log (2*(Nn:ℝ)) ≤ Real.log (4*P) := by
        apply Real.log_le_log (by positivity)
        linarith
      have hc0 : 0 ≤ cp := le_of_lt hcp
      have hfrac : cp * P / Real.log (4*P) ≤ cp * (Nn:ℝ) / Real.log (2*(Nn:ℝ)) := by
        rw [div_le_div_iff₀ hlog4P hlog1]
        have hA : cp*P ≤ cp*(Nn:ℝ) := mul_le_mul_of_nonneg_left hNn_ge hc0
        have hB : cp*P*Real.log (2*(Nn:ℝ)) ≤ cp*P*Real.log (4*P) :=
          mul_le_mul_of_nonneg_left hlog2 (mul_nonneg hc0 (le_of_lt hPpos))
        have hC : cp*P*Real.log (4*P) ≤ cp*(Nn:ℝ)*Real.log (4*P) :=
          mul_le_mul_of_nonneg_right hA (le_of_lt hlog4P)
        linarith
      linarith
    have hWpos : (0:ℝ) < (W.card:ℝ) :=
      lt_of_lt_of_le (by positivity : 0 < cp*P/Real.log (4*P)) hWcard
    set T13 : ℝ := p14T13 D R S ε with hT13
    have hT13pos : 0 < T13 := by rw [hT13]; exact p14T13_pos D R S hD hR hS ε
    have hT13nn : 0 ≤ T13 := le_of_lt hT13pos
    set L2 : ℝ := p14L2 R S α with hL2
    have hL2nn : 0 ≤ L2 := by rw [hL2]; exact P13b2_p14L2_nonneg R S α
    set Ener : ℝ := p14Ener R S α with hEnerDef
    have hEnernn : 0 ≤ Ener := by rw [hEnerDef]; exact P13b2_p14Ener_nonneg R S α
    have hEnerBnd : Ener ≤ KE * X^(ε/4) * L2 := by
      simpa [hEnerDef, hX, hL2] using hEner R S α hR hS
    set U : ℕ → ℝ := fun p => ∑ d ∈ Finset.Ioc D (2*D), Work.FIPlan.Evar R S (d*p^2) α with hU
    set Vp : ℕ → ℝ := fun p => ∑ d ∈ Finset.Ioc D (2*D), EvarB R S d p α with hVp
    have hUnn : ∀ p, 0 ≤ U p := fun p => Finset.sum_nonneg (fun d _ => P13b2_Evar_nonneg R S (d*p^2) α)
    have hVpnn : ∀ p, 0 ≤ Vp p := fun p => Finset.sum_nonneg (fun d _ => P13b2_EvarB_nonneg R S d p α)
    have hsumUnn : 0 ≤ ∑ p ∈ W, U p := Finset.sum_nonneg (fun p _ => hUnn p)
    have hsumVpnn : 0 ≤ ∑ p ∈ W, Vp p := Finset.sum_nonneg (fun p _ => hVpnn p)
    set B : ℝ := Kt * (8*X)^(ε/4) with hB
    have hBnn : 0 ≤ B := by rw [hB]; positivity
    have haf' := haf D R S hD hR hS hP1
    have haf1 : (D:ℝ)/P ≤ T13 := haf'.1
    have haf2 : 1/P ≤ T13 := haf'.2.1
    have haf3 : X/P^2 ≤ T13 := haf'.2.2.1
    have haf4 : Real.log (4*P) ≤ Kaf * X^(ε/8) := haf'.2.2.2.1
    -- ### Step 1: splitting each E(d) and averaging over p ∈ W
    have hVsplit : Work.FIPlan.Vvar R S D α
        ≤ (8*(Nn:ℝ)^2 * (∑ p ∈ W, U p) + 2 * (∑ p ∈ W, Vp p)) / (W.card:ℝ) := by
      have hsumV : (W.card:ℝ) * Work.FIPlan.Vvar R S D α = ∑ p ∈ W, Work.FIPlan.Vvar R S D α := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have hpoint : ∀ p ∈ W, Work.FIPlan.Vvar R S D α ≤ 2*(p:ℝ)^2 * U p + 2 * Vp p := by
        intro p hp
        have hpprime : Nat.Prime p := hWprime p hp
        have hper : ∀ d ∈ Finset.Ioc D (2*D),
            Work.FIPlan.Evar R S d α ≤ 2*(p:ℝ)^2 * Work.FIPlan.Evar R S (d*p^2) α + 2*EvarB R S d p α := by
          intro d hdmem
          have hd1 : 1 ≤ d := le_trans hD (le_of_lt (Finset.mem_Ioc.mp hdmem).1)
          calc Work.FIPlan.Evar R S d α
              ≤ 2*(EvarA R S d p α + EvarB R S d p α) := Evar_le_two_EvarA_add_EvarB R S d p α
            _ ≤ 2*((p:ℝ)^2 * Work.FIPlan.Evar R S (d*p^2) α + EvarB R S d p α) := by
                apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
                exact add_le_add (hea R S d p α hd1 hpprime) le_rfl
            _ = 2*(p:ℝ)^2 * Work.FIPlan.Evar R S (d*p^2) α + 2*EvarB R S d p α := by ring
        calc Work.FIPlan.Vvar R S D α
            = ∑ d ∈ Finset.Ioc D (2*D), Work.FIPlan.Evar R S d α := rfl
          _ ≤ ∑ d ∈ Finset.Ioc D (2*D),
                (2*(p:ℝ)^2 * Work.FIPlan.Evar R S (d*p^2) α + 2*EvarB R S d p α) :=
              Finset.sum_le_sum hper
          _ = 2*(p:ℝ)^2 * U p + 2 * Vp p := by
              rw [Finset.sum_add_distrib]
              rw [← Finset.mul_sum]
              rw [← Finset.mul_sum]
      have h1 : (W.card:ℝ) * Work.FIPlan.Vvar R S D α
          ≤ ∑ p ∈ W, (2*(p:ℝ)^2 * U p + 2 * Vp p) := by
        rw [hsumV]; exact Finset.sum_le_sum hpoint
      have hterm : ∑ p ∈ W, (2*(p:ℝ)^2 * U p + 2 * Vp p)
          ≤ 2 * (∑ p ∈ W, (p:ℝ)^2 * U p) + 2 * (∑ p ∈ W, Vp p) := by
        rw [Finset.sum_add_distrib]
        have hUterm : ∑ p ∈ W, 2*(p:ℝ)^2 * U p = 2 * (∑ p ∈ W, (p:ℝ)^2 * U p) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro p _; ring
        have hVterm : ∑ p ∈ W, 2 * Vp p = 2 * (∑ p ∈ W, Vp p) := by
          rw [Finset.mul_sum]
        rw [hUterm, hVterm]
      have hbd : ∑ p ∈ W, (2*(p:ℝ)^2 * U p + 2 * Vp p)
          ≤ 8*(Nn:ℝ)^2 * (∑ p ∈ W, U p) + 2 * (∑ p ∈ W, Vp p) := by
        have hsq : ∑ p ∈ W, (p:ℝ)^2 * U p ≤ (2*(Nn:ℝ))^2 * (∑ p ∈ W, U p) := by
          calc ∑ p ∈ W, (p:ℝ)^2 * U p
              ≤ ∑ p ∈ W, (2*(Nn:ℝ))^2 * U p := by
                apply Finset.sum_le_sum
                intro p hp
                have hp2 : (p:ℝ) ≤ 2*(Nn:ℝ) := by
                  exact_mod_cast ((hWmem p).mp hp).2.1
                have hp0 : (0:ℝ) ≤ (p:ℝ) := by positivity
                have : (p:ℝ)^2 ≤ (2*(Nn:ℝ))^2 := by nlinarith
                exact mul_le_mul_of_nonneg_right this (hUnn p)
            _ = (2*(Nn:ℝ))^2 * (∑ p ∈ W, U p) := by rw [Finset.mul_sum]
        have h2Nn : (2*(Nn:ℝ))^2 = 4*(Nn:ℝ)^2 := by ring
        linarith [hterm, hsq]
      rw [le_div_iff₀ hWpos]
      have h1' : Work.FIPlan.Vvar R S D α * (W.card:ℝ) = (W.card:ℝ) * Work.FIPlan.Vvar R S D α :=
        mul_comm _ _
      linarith [h1, hbd, h1']
    -- ### Step 2 (the U-sum): enlarging the moduli
    have hUp : ∑ p ∈ W, U p
        ≤ (Kaf2 * X^(ε/8)) * (3 * C121 * (Kns/P) * T13 * X^(ε/2) * Ener) := by
      have hA1 : 1 ≤ D*Nn^2 := by
        have := Nat.mul_pos (by omega : 0 < D) (by positivity : 0 < Nn^2)
        omega
      have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
      have he2ge1 : (1:ℝ) ≤ (((2*(2*(2*(D*Nn^2)))) : ℕ) : ℝ) := by
        have h1 : 1 ≤ 2*(2*(2*(D*Nn^2))) := by omega
        exact_mod_cast h1
      have he2le : (((2*(2*(2*(D*Nn^2)))) : ℕ) : ℝ) ≤ 32 * X^((3:ℝ)/4) := by
        have hcast : (((2*(2*(2*(D*Nn^2)))) : ℕ) : ℝ) = 8*(D:ℝ)*(Nn:ℝ)^2 := by
          push_cast; ring
        rw [hcast]
        have hNnsq : (Nn:ℝ)^2 ≤ 4*P^2 := by nlinarith [hNn_le, hNnpos]
        have hRS1 : (1:ℝ) ≤ (R:ℝ) + (S:ℝ) := by linarith
        have hpow : ((R:ℝ)+(S:ℝ))^(-(1:ℝ)/4) ≤ 1 := by
          calc ((R:ℝ)+(S:ℝ))^(-(1:ℝ)/4) ≤ ((R:ℝ)+(S:ℝ))^(0:ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hRS1 (by norm_num)
            _ = 1 := Real.rpow_zero _
        have hDP : (D:ℝ)*P^2 ≤ X^((3:ℝ)/4) := by
          have hpm := p13P_mul_sq D R S hD hR hS
          rw [← hP] at hpm
          rw [hpm, hX]
          have hstep1 : ((R:ℝ)+(S:ℝ))^(-(1:ℝ)/4) * ((R:ℝ)*(S:ℝ))^((3:ℝ)/4)
              ≤ 1 * ((R:ℝ)*(S:ℝ))^((3:ℝ)/4) :=
            mul_le_mul_of_nonneg_right hpow (by positivity : (0:ℝ) ≤ ((R:ℝ)*(S:ℝ))^((3:ℝ)/4))
          have hstep2 : (1:ℝ) * ((R:ℝ)*(S:ℝ))^((3:ℝ)/4) = ((R:ℝ)*(S:ℝ))^((3:ℝ)/4) := by ring
          exact le_trans hstep1 (le_of_eq hstep2)
        calc 8*(D:ℝ)*(Nn:ℝ)^2 = 8*((D:ℝ)*(Nn:ℝ)^2) := by ring
          _ ≤ 8*((D:ℝ)*(4*P^2)) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              exact mul_le_mul_of_nonneg_left hNnsq (le_of_lt hDpos)
          _ = 32*((D:ℝ)*P^2) := by ring
          _ ≤ 32*X^((3:ℝ)/4) := by linarith [hDP]
      have hlogX : Real.log X ≤ (8/ε) * X^(ε/8) :=
        P13b2_log_le_const_mul_rpow hε hX1
      have hlogbnd : Real.log ((((2*(2*(2*(D*Nn^2)))) : ℕ) : ℝ))
          ≤ (Real.log 32 + (3:ℝ)/4 * (8/ε)) * X^(ε/8) := by
        have h1 : Real.log ((((2*(2*(2*(D*Nn^2)))) : ℕ) : ℝ)) ≤ Real.log (32 * X^((3:ℝ)/4)) :=
          Real.log_le_log (by positivity) he2le
        have h2 : Real.log (32 * X^((3:ℝ)/4)) = Real.log 32 + ((3:ℝ)/4) * Real.log X := by
          rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hX0 _)), Real.log_rpow hX0]
        have hXe1 : (1:ℝ) ≤ X^(ε/8) := Real.one_le_rpow hX1 (by positivity)
        have hcomm : ((3:ℝ)/4) * ((8/ε) * X^(ε/8)) = ((3:ℝ)/4 * (8/ε)) * X^(ε/8) := by ring
        calc Real.log ((((2*(2*(2*(D*Nn^2)))) : ℕ) : ℝ))
            ≤ Real.log (32 * X^((3:ℝ)/4)) := h1
          _ = Real.log 32 + ((3:ℝ)/4) * Real.log X := h2
          _ ≤ Real.log 32 + ((3:ℝ)/4) * ((8/ε) * X^(ε/8)) := by
              have hc : ((3:ℝ)/4) * Real.log X ≤ ((3:ℝ)/4) * ((8/ε) * X^(ε/8)) :=
                mul_le_mul_of_nonneg_left hlogX (by norm_num)
              linarith
          _ ≤ (Real.log 32 + (3:ℝ)/4 * (8/ε)) * X^(ε/8) := by
              rw [hcomm]
              have h32 : Real.log 32 ≤ Real.log 32 * X^(ε/8) := by
                have := mul_le_mul_of_nonneg_left hXe1
                  (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 32))
                simpa using this
              have hexp : (Real.log 32 + (3:ℝ)/4 * (8/ε)) * X^(ε/8)
                  = Real.log 32 * X^(ε/8) + ((3:ℝ)/4 * (8/ε)) * X^(ε/8) := by ring
              rw [hexp]
              linarith
      have hFbound : Real.log ((((2*(2*(2*(D*Nn^2)))) : ℕ) : ℝ))/Real.log 4 + 2
          ≤ Kaf2 * X^(ε/8) := by
        have h1 : Real.log ((((2*(2*(2*(D*Nn^2)))) : ℕ) : ℝ))/Real.log 4
            ≤ ((Real.log 32 + (3:ℝ)/4 * (8/ε))/Real.log 4) * X^(ε/8) := by
          rw [div_mul_eq_mul_div]
          exact (div_le_div_iff_of_pos_right hlog4pos).mpr hlogbnd
        have h2 : (2:ℝ) ≤ 2 * X^(ε/8) := by
          have hx : (1:ℝ) ≤ X^(ε/8) := Real.one_le_rpow hX1 (by positivity)
          linarith
        calc Real.log ((((2*(2*(2*(D*Nn^2)))) : ℕ) : ℝ))/Real.log 4 + 2
            ≤ ((Real.log 32 + (3:ℝ)/4 * (8/ε))/Real.log 4) * X^(ε/8) + 2 := by linarith
          _ ≤ ((Real.log 32 + (3:ℝ)/4 * (8/ε))/Real.log 4) * X^(ε/8) + 2 * X^(ε/8) := by
              linarith
          _ = Kaf2 * X^(ε/8) := by rw [hKaf2]; ring
      have hlo : ∀ p ∈ W, ∀ d ∈ Finset.Ioc D (2*D), D*Nn^2 < d*p^2 := by
        intro p hp d hd
        have hpN : Nn < p := ((hWmem p).mp hp).1
        have hDd : D < d := (Finset.mem_Ioc.mp hd).1
        have hNnsq_pos : 0 < Nn^2 := by positivity
        have h1 : D * Nn^2 < (D+1) * Nn^2 := Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self D) hNnsq_pos
        have h2 : (D+1) * Nn^2 ≤ d * Nn^2 := Nat.mul_le_mul_right (Nn^2) (Nat.succ_le_of_lt hDd)
        have h3 : d * Nn^2 ≤ d * p^2 := Nat.mul_le_mul_left d (Nat.pow_le_pow_left (le_of_lt hpN) 2)
        exact lt_of_lt_of_le (lt_of_lt_of_le h1 h2) h3
      have hhi : ∀ p ∈ W, ∀ d ∈ Finset.Ioc D (2*D), d*p^2 ≤ 2*(2*(2*(D*Nn^2))) := by
        intro p hp d hd
        have hp2N : p ≤ 2*Nn := ((hWmem p).mp hp).2.1
        have hd2D : d ≤ 2*D := (Finset.mem_Ioc.mp hd).2
        calc d*p^2 ≤ (2*D)*(2*Nn)^2 := Nat.mul_le_mul hd2D (Nat.pow_le_pow_left hp2N 2)
          _ = 2*(2*(2*(D*Nn^2))) := by ring
      have hhm : ∑ p ∈ W, U p
          ≤ (Real.log ((((2*(2*(2*(D*Nn^2)))) : ℕ) : ℝ))/Real.log 4 + 2)
              * ∑ e ∈ Finset.Ioc (D*Nn^2) (2*(2*(2*(D*Nn^2)))), Work.FIPlan.Evar R S e α :=
        hm D R S W α (D*Nn^2) (2*(2*(2*(D*Nn^2)))) hA1 hWprime hlo hhi
      have hsplit : ∑ e ∈ Finset.Ioc (D*Nn^2) (2*(2*(2*(D*Nn^2)))), Work.FIPlan.Evar R S e α
          = Work.FIPlan.Vvar R S (D*Nn^2) α + Work.FIPlan.Vvar R S (2*(D*Nn^2)) α
            + Work.FIPlan.Vvar R S (2*(2*(D*Nn^2))) α := by
        rw [P13b2_sum_dyadic (D*Nn^2) (fun e => Work.FIPlan.Evar R S e α)]
        rfl
      have hcast : ∀ k : ℕ, ((k*(D*Nn^2) : ℕ):ℝ) = (k:ℝ)*(D:ℝ)*(Nn:ℝ)^2 := by
        intro k; push_cast; ring
      have hlo_g : ∀ k : ℕ, 1 ≤ k → (D:ℝ)*P^2/2 ≤ ((k*(D*Nn^2):ℕ):ℝ) := by
        intro k hk
        rw [hcast]
        have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
        have hPN : P^2 ≤ (Nn:ℝ)^2 := by nlinarith [hNn_ge, hPpos]
        have h1 : (D:ℝ)*P^2 ≤ (D:ℝ)*(Nn:ℝ)^2 := mul_le_mul_of_nonneg_left hPN (le_of_lt hDpos)
        have h2 : (D:ℝ)*(Nn:ℝ)^2 ≤ (k:ℝ)*(D:ℝ)*(Nn:ℝ)^2 := by
          have hkD : (D:ℝ) ≤ (k:ℝ)*(D:ℝ) := by
            calc (D:ℝ) = 1*(D:ℝ) := by ring
              _ ≤ (k:ℝ)*(D:ℝ) := mul_le_mul_of_nonneg_right hkR (le_of_lt hDpos)
          calc (D:ℝ)*(Nn:ℝ)^2 ≤ ((k:ℝ)*(D:ℝ))*(Nn:ℝ)^2 :=
                mul_le_mul_of_nonneg_right hkD (by positivity)
            _ = (k:ℝ)*(D:ℝ)*(Nn:ℝ)^2 := by ring
        have hDPnn : (0:ℝ) ≤ (D:ℝ)*P^2 := by positivity
        linarith [h1, h2, hDPnn]
      have hhi_g : ∀ k : ℕ, k ≤ 4 → ((k*(D*Nn^2):ℕ):ℝ) ≤ 16*(D:ℝ)*P^2 := by
        intro k hk
        rw [hcast]
        have hkR : (k:ℝ) ≤ 4 := by exact_mod_cast hk
        have hNn_sq : (Nn:ℝ)^2 ≤ 4*P^2 := by nlinarith [hNn_le, hNnpos]
        calc (k:ℝ)*(D:ℝ)*(Nn:ℝ)^2 ≤ 4*(D:ℝ)*(4*P^2) := by
              apply mul_le_mul _ hNn_sq (by positivity) (by positivity)
              nlinarith [hkR, le_of_lt hDpos]
          _ = 16*(D:ℝ)*P^2 := by ring
      have hbgen : ∀ A : ℕ, 1 ≤ A → (D:ℝ)*P^2/2 ≤ (A:ℝ) → (A:ℝ) ≤ 16*(D:ℝ)*P^2 →
          Work.FIPlan.Vvar R S A α ≤ C121 * (Kns/P) * T13 * X^(ε/2) * Ener := by
        intro A hA1 hAlo hAhi
        have h121A := h121 A R S α hA1 hR hS hsup
        have hnsA := hns D R S P A hD hR hS rfl hP1 hA1 hAlo hAhi
        calc Work.FIPlan.Vvar R S A α
            ≤ C121 * p14T12 A R S (ε/8) * p14Ener R S α := h121A
          _ ≤ C121 * (Kns * T13 * X^(ε/2) / P) * Ener := by
              apply mul_le_mul_of_nonneg_right _ hEnernn
              apply mul_le_mul_of_nonneg_left _ (le_of_lt hC121)
              rw [le_div_iff₀ hPpos]
              nlinarith [hnsA]
          _ = C121 * (Kns/P) * T13 * X^(ε/2) * Ener := by ring
      have hA3 : 1 ≤ 2*(2*(D*Nn^2)) := by omega
      have hlo1 : (D:ℝ)*P^2/2 ≤ ((D*Nn^2:ℕ):ℝ) := by
        have h := hlo_g 1 le_rfl; simpa using h
      have hhi1 : ((D*Nn^2:ℕ):ℝ) ≤ 16*(D:ℝ)*P^2 := by
        have h := hhi_g 1 (by norm_num); simpa using h
      have hlo4 : (D:ℝ)*P^2/2 ≤ ((2*(2*(D*Nn^2)):ℕ):ℝ) := by
        have h := hlo_g 4 (by norm_num)
        have he : (4*(D*Nn^2) : ℕ) = 2*(2*(D*Nn^2)) := by ring
        rwa [he] at h
      have hhi4 : ((2*(2*(D*Nn^2)):ℕ):ℝ) ≤ 16*(D:ℝ)*P^2 := by
        have h := hhi_g 4 le_rfl
        have he : (4*(D*Nn^2) : ℕ) = 2*(2*(D*Nn^2)) := by ring
        rwa [he] at h
      have hb1 := hbgen (D*Nn^2) hA1 hlo1 hhi1
      have hb2 := hbgen (2*(D*Nn^2)) (by omega) (hlo_g 2 (by norm_num)) (hhi_g 2 (by norm_num))
      have hb3 := hbgen (2*(2*(D*Nn^2))) hA3 hlo4 hhi4
      have hsumE : 0 ≤ ∑ e ∈ Finset.Ioc (D*Nn^2) (2*(2*(2*(D*Nn^2)))), Work.FIPlan.Evar R S e α :=
        Finset.sum_nonneg (fun e _ => P13b2_Evar_nonneg R S e α)
      have hhm' : ∑ p ∈ W, U p
          ≤ (Kaf2 * X^(ε/8))
              * ∑ e ∈ Finset.Ioc (D*Nn^2) (2*(2*(2*(D*Nn^2)))), Work.FIPlan.Evar R S e α :=
        le_trans hhm (mul_le_mul_of_nonneg_right hFbound hsumE)
      have hKaf2pos : (0:ℝ) < Kaf2 := by rw [hKaf2]; positivity
      have hKFacnn : 0 ≤ Kaf2 * X^(ε/8) :=
        mul_nonneg (le_of_lt hKaf2pos) (Real.rpow_nonneg (le_of_lt hX0) _)
      calc ∑ p ∈ W, U p
          ≤ (Kaf2 * X^(ε/8))
              * ∑ e ∈ Finset.Ioc (D*Nn^2) (2*(2*(2*(D*Nn^2)))), Work.FIPlan.Evar R S e α := hhm'
        _ = (Kaf2 * X^(ε/8))
              * (Work.FIPlan.Vvar R S (D*Nn^2) α + Work.FIPlan.Vvar R S (2*(D*Nn^2)) α
                + Work.FIPlan.Vvar R S (2*(2*(D*Nn^2))) α) := by rw [hsplit]
        _ ≤ (Kaf2 * X^(ε/8))
              * (C121*(Kns/P)*T13*X^(ε/2)*Ener + C121*(Kns/P)*T13*X^(ε/2)*Ener
                + C121*(Kns/P)*T13*X^(ε/2)*Ener) := by
              apply mul_le_mul_of_nonneg_left _ hKFacnn
              linarith [hb1, hb2, hb3]
        _ = (Kaf2 * X^(ε/8)) * (3 * C121 * (Kns/P) * T13 * X^(ε/2) * Ener) := by ring
    -- ### Step 3 (the V-sum): the trivial bound for the `p ∣ r` part
    have hVp : ∑ p ∈ W, Vp p ≤ (D + B*(4*X/(Nn:ℝ)+4)) * (Kpd*X^(ε/8)) * L2 := by
      have hBbound : ∀ m : ℕ, 1 ≤ m → m ≤ 8*R*S → ((m.divisors.card:ℕ):ℝ) ≤ B := by
        intro m hm1 hm8
        have hτ := htau m hm1
        have hmle : (m:ℝ) ≤ 8*X := by
          have hcast : ((8*R*S : ℕ):ℝ) = 8*X := by push_cast; rw [hX]; ring
          calc (m:ℝ) ≤ ((8*R*S : ℕ):ℝ) := by exact_mod_cast hm8
            _ = 8*X := hcast
        have hpow : (m:ℝ)^(ε/4) ≤ (8*X)^(ε/4) :=
          Real.rpow_le_rpow (by positivity) hmle (by positivity)
        calc ((m.divisors.card:ℕ):ℝ) ≤ Kt * (m:ℝ)^(ε/4) := hτ
          _ ≤ Kt * (8*X)^(ε/4) := mul_le_mul_of_nonneg_left hpow (le_of_lt hKt)
          _ = B := rfl
      have hVp' : ∀ p ∈ W, Vp p ≤ (D + B*(4*X/(p:ℝ)+4)) * L2p R S p α := by
        intro p hp
        have h := heb D R S p α B (hWprime p hp).one_le hBbound hsup
        have heq : (4 * (R:ℝ) * (S:ℝ) / (p:ℝ) + 4) = (4*X/(p:ℝ)+4) := by rw [hX]; ring
        rw [heq] at h
        simpa [hVp] using h
      have hVp'' : ∑ p ∈ W, Vp p ≤ (D + B*(4*X/(Nn:ℝ)+4)) * (∑ p ∈ W, L2p R S p α) := by
        calc ∑ p ∈ W, Vp p
            ≤ ∑ p ∈ W, (D + B*(4*X/(p:ℝ)+4)) * L2p R S p α := Finset.sum_le_sum hVp'
          _ ≤ ∑ p ∈ W, (D + B*(4*X/(Nn:ℝ)+4)) * L2p R S p α := by
              apply Finset.sum_le_sum
              intro p hp
              have hpN : Nn < p := ((hWmem p).mp hp).1
              have hpge : (Nn:ℝ) ≤ (p:ℝ) := by exact_mod_cast (le_of_lt hpN)
              have hpRpos : (0:ℝ) < (p:ℝ) := by exact_mod_cast (hWprime p hp).pos
              have hle : 4*X/(p:ℝ) ≤ 4*X/(Nn:ℝ) := by
                rw [div_le_div_iff₀ hpRpos hNnpos]
                nlinarith [hpge, le_of_lt hX0]
              have hfac : D + B*(4*X/(p:ℝ)+4) ≤ D + B*(4*X/(Nn:ℝ)+4) := by
                nlinarith [hle, hBnn]
              exact mul_le_mul_of_nonneg_right hfac (P13b2_L2p_nonneg R S p α)
          _ = (D + B*(4*X/(Nn:ℝ)+4)) * (∑ p ∈ W, L2p R S p α) := by rw [Finset.mul_sum]
      have hL2psum : ∑ p ∈ W, L2p R S p α ≤ (Kpd*X^(ε/8)) * L2 := by
        have h := hL2p R S α W (Kpd*X^(ε/8)) (by positivity)
          (fun r hr1 hr2R => by simpa [hX] using hpd R S Nn r hR hS hr1 hr2R)
        simpa [hL2] using h
      calc ∑ p ∈ W, Vp p
          ≤ (D + B*(4*X/(Nn:ℝ)+4)) * (∑ p ∈ W, L2p R S p α) := hVp''
        _ ≤ (D + B*(4*X/(Nn:ℝ)+4)) * ((Kpd*X^(ε/8)) * L2) :=
            mul_le_mul_of_nonneg_left hL2psum (by positivity)
        _ = (D + B*(4*X/(Nn:ℝ)+4)) * (Kpd*X^(ε/8)) * L2 := by ring
    -- ### Step 4: the arithmetic of the U-part
    have hNn2W : 8*(Nn:ℝ)^2 / (W.card:ℝ) ≤ 32*P*Kaf*X^(ε/8)/cp := by
      have hcpP : (0:ℝ) < cp*P := by positivity
      have hinv : 1/(W.card:ℝ) ≤ Real.log (4*P)/(cp*P) := by
        rw [div_le_div_iff₀ hWpos hcpP]
        have h := hWcard
        rw [div_le_iff₀ hlog4P] at h
        linarith
      have hNnsq : (Nn:ℝ)^2 ≤ 4*P^2 := by nlinarith [hNn_le, hNnpos]
      calc 8*(Nn:ℝ)^2/(W.card:ℝ) = 8*(Nn:ℝ)^2 * (1/(W.card:ℝ)) := by ring
        _ ≤ 8*(Nn:ℝ)^2 * (Real.log (4*P)/(cp*P)) := mul_le_mul_of_nonneg_left hinv (by positivity)
        _ ≤ 8*(4*P^2) * (Real.log (4*P)/(cp*P)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            nlinarith [hNnsq]
        _ = (32*P/cp) * Real.log (4*P) := by field_simp; ring
        _ ≤ (32*P/cp) * (Kaf*X^(ε/8)) := by
            apply mul_le_mul_of_nonneg_left haf4 (by positivity)
        _ = 32*P*Kaf*X^(ε/8)/cp := by ring
    have hUbound : (8*(Nn:ℝ)^2 / (W.card:ℝ)) * (∑ p ∈ W, U p)
        ≤ (96*C121*Kns*KE*Kaf*Kaf2/cp) * T13 * X^ε * L2 := by
      have hfac : (0:ℝ) ≤ 32*P*Kaf*X^(ε/8)/cp := by positivity
      have h1 := mul_le_mul_of_nonneg_right hNn2W hsumUnn
      have h2 := mul_le_mul_of_nonneg_left hUp hfac
      have h3a : (32*P*Kaf*X^(ε/8)/cp) * (3*C121*(Kns/P)*T13*X^(ε/2)*Ener)
          = 96*C121*Kns*Kaf/cp * T13 * (X^(ε/8)*X^(ε/2)) * Ener := by
        field_simp
        ring
      have h3b : (32*P*Kaf*X^(ε/8)/cp)
            * ((Kaf2*X^(ε/8)) * (3*C121*(Kns/P)*T13*X^(ε/2)*Ener))
          = (Kaf2*X^(ε/8))
            * ((32*P*Kaf*X^(ε/8)/cp) * (3*C121*(Kns/P)*T13*X^(ε/2)*Ener)) := by ring
      have h3 : (32*P*Kaf*X^(ε/8)/cp)
            * ((Kaf2*X^(ε/8)) * (3*C121*(Kns/P)*T13*X^(ε/2)*Ener))
          = 96*C121*Kns*Kaf*Kaf2/cp * T13 * (X^(ε/8)*X^(ε/8)*X^(ε/2)) * Ener := by
        rw [h3b, h3a]; ring
      have hXcomb : X^(ε/8)*X^(ε/8)*X^(ε/2) = X^(3*ε/4) := by
        rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]; congr 1; ring
      calc (8*(Nn:ℝ)^2 / (W.card:ℝ)) * (∑ p ∈ W, U p)
          ≤ (32*P*Kaf*X^(ε/8)/cp)*(∑ p ∈ W, U p) := h1
        _ ≤ (32*P*Kaf*X^(ε/8)/cp)
              * ((Kaf2*X^(ε/8))*(3*C121*(Kns/P)*T13*X^(ε/2)*Ener)) := h2
        _ = 96*C121*Kns*Kaf*Kaf2/cp * T13
              * (X^(ε/8)*X^(ε/8)*X^(ε/2)) * Ener := h3
        _ = 96*C121*Kns*Kaf*Kaf2/cp * T13 * X^(3*ε/4) * Ener := by rw [hXcomb]
        _ ≤ 96*C121*Kns*Kaf*Kaf2/cp * T13 * X^(3*ε/4) * (KE * X^(ε/4) * L2) :=
            mul_le_mul_of_nonneg_left hEnerBnd (by positivity)
        _ = 96*C121*Kns*KE*Kaf*Kaf2/cp * T13 * (X^(3*ε/4)*X^(ε/4)) * L2 := by ring
        _ = 96*C121*Kns*KE*Kaf*Kaf2/cp * T13 * X^ε * L2 := by
            rw [show X^(3*ε/4)*X^(ε/4) = X^ε from by
              rw [← Real.rpow_add hX0]; congr 1; ring]
    -- ### Step 5: the arithmetic of the V-part
    have harith : (D + B*(4*X/(Nn:ℝ)+4))/P ≤ (1 + 8*Kt*(8:ℝ)^(ε/4))*T13*X^(ε/4) := by
      rw [div_le_iff₀ hPpos]
      have hDle : (D:ℝ) ≤ T13 * P := by
        have h := haf1; rw [div_le_iff₀ hPpos] at h; linarith
      have h1le : (1:ℝ) ≤ T13 * P := by
        have h := haf2; rw [div_le_iff₀ hPpos] at h; linarith
      have hXle : X ≤ T13 * P^2 := by
        have h := haf3; rw [div_le_iff₀ (by positivity : (0:ℝ) < P^2)] at h; linarith
      have hXNn : X/Nn ≤ T13*P := by
        have h1 : X/Nn ≤ X/P :=
          div_le_div_of_nonneg_left (by positivity : (0:ℝ) ≤ X) hPpos hNn_ge
        have h2 : X/P ≤ T13*P := by
          rw [div_le_iff₀ hPpos]; nlinarith [hXle]
        linarith
      have hBexpand : B = Kt * (8:ℝ)^(ε/4) * X^(ε/4) := by
        rw [hB, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 8) (le_of_lt hX0)]; ring
      have hXe4 : (1:ℝ) ≤ X^(ε/4) := Real.one_le_rpow hX1 (by positivity)
      have hkey : 1 + 8*B ≤ (1 + 8*Kt*(8:ℝ)^(ε/4)) * X^(ε/4) := by
        rw [hBexpand]
        nlinarith [hXe4, hKt, h8pow]
      calc D + B*(4*X/(Nn:ℝ)+4)
          = D + 4*B*(X/Nn) + 4*B := by ring
        _ ≤ T13*P + 4*B*(T13*P) + 4*B*(T13*P) := by
            apply add_le_add (add_le_add hDle ?_) ?_
            · exact mul_le_mul_of_nonneg_left hXNn (by positivity)
            · calc 4*B = 4*B*1 := by ring
                _ ≤ 4*B*(T13*P) := mul_le_mul_of_nonneg_left h1le (by positivity)
        _ = T13*P*(1 + 8*B) := by ring
        _ ≤ T13*P*((1 + 8*Kt*(8:ℝ)^(ε/4))*X^(ε/4)) :=
            mul_le_mul_of_nonneg_left hkey (by positivity)
        _ = (1 + 8*Kt*(8:ℝ)^(ε/4))*T13*X^(ε/4)*P := by ring
    have hinv2 : 2/(W.card:ℝ) ≤ 2*Real.log (4*P)/(cp*P) := by
      rw [div_le_div_iff₀ hWpos (by positivity : (0:ℝ) < cp*P)]
      have h := hWcard
      rw [div_le_iff₀ hlog4P] at h
      nlinarith [h]
    have hVbound : (2/(W.card:ℝ)) * (∑ p ∈ W, Vp p)
        ≤ (2*Kaf*Kpd/cp)*(1+8*Kt*(8:ℝ)^(ε/4)) * T13 * X^ε * L2 := by
      have h1 : (2/(W.card:ℝ)) * (∑ p ∈ W, Vp p)
          ≤ (2*Real.log (4*P)/(cp*P)) * (∑ p ∈ W, Vp p) :=
        mul_le_mul_of_nonneg_right hinv2 hsumVpnn
      have h2 : (2*Real.log (4*P)/(cp*P)) * (∑ p ∈ W, Vp p)
          ≤ (2*Real.log (4*P)/(cp*P)) * ((D + B*(4*X/(Nn:ℝ)+4)) * (Kpd*X^(ε/8)) * L2) :=
        mul_le_mul_of_nonneg_left hVp (by positivity)
      have h3 : (2*Real.log (4*P)/(cp*P)) * ((D + B*(4*X/(Nn:ℝ)+4)) * (Kpd*X^(ε/8)) * L2)
          = (2*Real.log (4*P)/cp) * (((D + B*(4*X/(Nn:ℝ)+4))/P) * (Kpd*X^(ε/8)) * L2) := by
        ring
      have h4 : (2*Real.log (4*P)/cp) * (((D + B*(4*X/(Nn:ℝ)+4))/P) * (Kpd*X^(ε/8)) * L2)
          ≤ (2*Real.log (4*P)/cp)
              * (((1 + 8*Kt*(8:ℝ)^(ε/4))*T13*X^(ε/4)) * (Kpd*X^(ε/8)) * L2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hL2nn
        exact mul_le_mul_of_nonneg_right harith (by positivity)
      have h5 : (2*Real.log (4*P)/cp)
            * (((1 + 8*Kt*(8:ℝ)^(ε/4))*T13*X^(ε/4)) * (Kpd*X^(ε/8)) * L2)
          ≤ (2*Kaf*X^(ε/8)/cp)
            * (((1 + 8*Kt*(8:ℝ)^(ε/4))*T13*X^(ε/4)) * (Kpd*X^(ε/8)) * L2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply div_le_div_of_nonneg_right _ (le_of_lt hcp)
        calc 2*Real.log (4*P) = 2*(Real.log (4*P)) := by ring
          _ ≤ 2*(Kaf*X^(ε/8)) := mul_le_mul_of_nonneg_left haf4 (by norm_num)
          _ = 2*Kaf*X^(ε/8) := by ring
      have hXhalf : X^(ε/2) ≤ X^ε := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      calc (2/(W.card:ℝ)) * (∑ p ∈ W, Vp p)
          ≤ (2*Real.log (4*P)/(cp*P)) * (∑ p ∈ W, Vp p) := h1
        _ ≤ (2*Real.log (4*P)/(cp*P)) * ((D + B*(4*X/(Nn:ℝ)+4)) * (Kpd*X^(ε/8)) * L2) := h2
        _ = (2*Real.log (4*P)/cp) * (((D + B*(4*X/(Nn:ℝ)+4))/P) * (Kpd*X^(ε/8)) * L2) := h3
        _ ≤ (2*Real.log (4*P)/cp)
              * (((1 + 8*Kt*(8:ℝ)^(ε/4))*T13*X^(ε/4)) * (Kpd*X^(ε/8)) * L2) := h4
        _ ≤ (2*Kaf*X^(ε/8)/cp)
              * (((1 + 8*Kt*(8:ℝ)^(ε/4))*T13*X^(ε/4)) * (Kpd*X^(ε/8)) * L2) := h5
        _ = (2*Kaf*Kpd/cp)*(1+8*Kt*(8:ℝ)^(ε/4)) * T13 * (X^(ε/4)*X^(ε/8)*X^(ε/8)) * L2 := by
            ring
        _ = (2*Kaf*Kpd/cp)*(1+8*Kt*(8:ℝ)^(ε/4)) * T13 * X^(ε/2) * L2 := by
            rw [show X^(ε/4)*X^(ε/8)*X^(ε/8) = X^(ε/2) from by
              rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]; congr 1; ring]
        _ ≤ (2*Kaf*Kpd/cp)*(1+8*Kt*(8:ℝ)^(ε/4)) * T13 * X^ε * L2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hXhalf (by positivity)) hL2nn
    -- ### Step 6: putting the two parts together
    calc Work.FIPlan.Vvar R S D α
        ≤ (8*(Nn:ℝ)^2 * (∑ p ∈ W, U p) + 2 * (∑ p ∈ W, Vp p)) / (W.card:ℝ) := hVsplit
      _ = (8*(Nn:ℝ)^2/(W.card:ℝ)) * (∑ p ∈ W, U p)
            + (2/(W.card:ℝ)) * (∑ p ∈ W, Vp p) := by ring
      _ ≤ (96*C121*Kns*KE*Kaf*Kaf2/cp) * T13 * X^ε * L2
            + (2*Kaf*Kpd/cp)*(1+8*Kt*(8:ℝ)^(ε/4)) * T13 * X^ε * L2 :=
          add_le_add hUbound hVbound
      _ = (96*C121*Kns*KE*Kaf*Kaf2/cp
            + (2*Kaf*Kpd/cp)*(1+8*Kt*(8:ℝ)^(ε/4))) * T13 * X^ε * L2 := by
          ring

end

end Work.FIArea4
