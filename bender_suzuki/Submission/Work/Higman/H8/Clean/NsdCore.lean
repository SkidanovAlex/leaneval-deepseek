import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.H8.Clean.NsdTransfer
import Submission.Work.Higman.c4_field_core
import Submission.Work.Higman.omega1_iso_field
import Submission.Work.Higman.higman_lemma2
import Submission.Work.Higman.c4_lam_ne_mu
import Submission.Work.Higman.H8.Clean.NsdL1
import Submission.Work.Higman.center_eq_omega1_new

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.Higman.H8.Clean

variable {P : Type} [Group P] [Finite P]

/-! ## Auxiliary facts about the quotient `P ⧸ A` -/

/-- Multiplicativity of the quotient map. -/
theorem quot_mk_mul {A : Subgroup P} [A.Normal] (u v : P) :
    ((u * v : P) : P ⧸ A) = (u : P ⧸ A) * (v : P ⧸ A) := by
  simpa [QuotientGroup.mk'_apply] using map_mul (QuotientGroup.mk' A) u v

/-- Two elements with the same image in `P ⧸ A` differ by an element of `A`. -/
theorem exists_mul_mem_of_quot_eq {A : Subgroup P} [A.Normal] {u v : P}
    (h : (u : P ⧸ A) = (v : P ⧸ A)) : ∃ t ∈ A, u = v * t :=
  ⟨v⁻¹ * u, QuotientGroup.eq.mp h.symm, by group⟩

/-- Two elements of the abelian subgroup `A` with the same square differ by an element of
`A ^ (2)`. -/
theorem mul_inv_mem_powSub_two_of_sq_eq (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (htop : powSub A 2 = omega1 P) {a b : P} (ha : a ∈ A) (hb : b ∈ A)
    (hsqeq : a * a = b * b) : a * b⁻¹ ∈ powSub A 2 := by
  have hcomm : b⁻¹ * a = a * b⁻¹ := (hAab a ha b⁻¹ (A.inv_mem hb)).symm
  have h2 : (a * b⁻¹) * (a * b⁻¹) = (a * a) * ((b * b)⁻¹) := by
    rw [show (a * b⁻¹) * (a * b⁻¹) = a * (b⁻¹ * a) * b⁻¹ from by group, hcomm]
    group
  have h1 : (a * b⁻¹) * (a * b⁻¹) = 1 := by
    rw [h2, hsqeq, mul_inv_cancel]
  have h3 : a * b⁻¹ ∈ omega1 P := h.mem_omega1.mpr (by rwa [pow_two])
  rwa [← htop] at h3

/-- If every square of `P` lies in `A ^ (2)`, then every commutator lies in `A ^ (2)`
(the squaring identity `(uv)² = [u,[v,u]]·([v,u]·u²·v²)`, cf. `powSub_C_eq_of_cover`). -/
theorem comm_mem_powSub_two_of_sq_mem (h : IsSuzuki2Grp P) {A : Subgroup P} [hAn : A.Normal]
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq2 : ∀ x : P, x ^ 2 ∈ powSub A 2) (u v : P) :
    ⁅u, v⁆ ∈ powSub A 2 := by
  have hA : IsXiAbelNormal h A := ⟨hAn, hAxi, hAab⟩
  have hvu : ⁅v, u⁆ ∈ A := by
    rw [← hGs, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top v) (Subgroup.mem_top u)
  have hχ : ⁅u, ⁅v, u⁆⁆ ∈ powSub A 2 := commutator_mem_powSub_two h hA u ⁅v, u⁆ hvu
  have hone : (u * v) * (u * v) = ⁅u, ⁅v, u⁆⁆ * (⁅v, u⁆ * (u * u) * (v * v)) := by
    simp only [commutatorElement_def]; group
  have h1 : (u * v) * (u * v) ∈ powSub A 2 := by
    have h2 := hsq2 (u * v); rwa [pow_two] at h2
  have hu2 : u * u ∈ powSub A 2 := by have h2 := hsq2 u; rwa [pow_two] at h2
  have hv2 : v * v ∈ powSub A 2 := by have h2 := hsq2 v; rwa [pow_two] at h2
  have h3 : ⁅v, u⁆ = (⁅u, ⁅v, u⁆⁆)⁻¹ * ((u * v) * (u * v)) * ((v * v)⁻¹ * (u * u)⁻¹) := by
    rw [hone]; group
  have hmem : ⁅v, u⁆ ∈ powSub A 2 := by
    rw [h3]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ((powSub A 2).inv_mem hχ) h1)
      (Subgroup.mul_mem _ ((powSub A 2).inv_mem hv2) ((powSub A 2).inv_mem hu2))
  have hsym : ⁅u, v⁆ = (⁅v, u⁆)⁻¹ := by
    rw [commutatorElement_def, commutatorElement_def]; group
  rw [hsym]
  exact (powSub A 2).inv_mem hmem

/-- In a finite field of order `2 ^ n`, an element of multiplicative order `2 ^ n - 1` generates
the multiplicative group: every non-zero element is one of its powers. -/
theorem pow_exhaust_of_orderOf_card {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {lam : F} (hlam : orderOf lam = Fintype.card F - 1) {x : F} (hx : x ≠ 0) :
    ∃ s : ℕ, lam ^ s = x := by
  have hne : lam ≠ 0 := by
    intro h0
    rw [h0, orderOf_zero F] at hlam
    have h1 : Fintype.card F ≤ 1 := by omega
    have h2 : 2 ≤ Fintype.card F :=
      Fintype.one_lt_card_iff_nontrivial.mpr ⟨0, 1, zero_ne_one⟩
    omega
  set N := Fintype.card F - 1 with hN
  have hNcard : Fintype.card F = N + 1 := by rw [hN]; exact (Nat.succ_pred_eq_of_pos Fintype.card_pos).symm
  have hinj : Set.InjOn (fun s : ℕ => lam ^ s) (Set.Iio N) := by
    rw [← hlam]; exact pow_injOn_Iio_orderOf
  have hS : ((Finset.range N).image (fun s => lam ^ s)).card = N := by
    rw [Finset.card_image_of_injOn (fun a ha b hb h =>
        hinj (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) h), Finset.card_range]
  have hsub : (Finset.range N).image (fun s => lam ^ s) ⊆
      (Finset.univ : Finset F).erase 0 := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨s, -, rfl⟩ := hz
    exact Finset.mem_erase.mpr ⟨pow_ne_zero _ hne, Finset.mem_univ _⟩
  have heq : (Finset.range N).image (fun s => lam ^ s) = (Finset.univ : Finset F).erase 0 := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    have hc : ((Finset.univ : Finset F).erase 0).card = N := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : F)), Finset.card_univ, hN]
    rw [hc, hS]
  have hxmem : x ∈ (Finset.univ : Finset F).erase 0 :=
    Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩
  rw [← heq, Finset.mem_image] at hxmem
  obtain ⟨s, -, hs⟩ := hxmem
  exact ⟨s, hs⟩

/-! ## The abstract core -/

/-- **The core of the `C₄` exclusion.**  Suppose `A` is the derived subgroup of the Suzuki
2-group `P`, `A` is abelian of exponent `4` with `Ω₁(P) = A²` and `|A| = |Ω₁(P)|²`, and the two
layers `P/A` and `Ω₁(P)` are identified (through a common finite field `F` of order `2 ^ n`) with
`F` in such a way that `ξ` acts by multiplication by `lam` on the first and by multiplication by
`mu` on the second.  Then we reach a contradiction (this is the eigenvalue bookkeeping of
Higman's Lemma 6, formalised as `Work.Higman.c4_field_core`). -/
theorem nsd_core {P : Type} [Group P] [Finite P] (h : IsSuzuki2Grp P) {A : Subgroup P}
    [hAn : A.Normal]
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : powSub A 4 = ⊥) (htop : powSub A 2 = omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(omega1 P)) ^ 2)
    (hcent : ∀ u : P, u ∉ A → ∃ a ∈ A, ⁅u, a⁆ ≠ 1)
    {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (hFcard : Fintype.card F = 2 ^ n) (hZcard : Nat.card ↥(omega1 P) = 2 ^ n)
    (lam mu : F) (hlamord : orderOf lam = 2 ^ n - 1) (hmuord : orderOf mu = 2 ^ n - 1)
    (ζV : F ≃ (P ⧸ A))
    (hζVadd : ∀ x y : F, ζV (x + y) = ζV x * ζV y)
    (hζVeq : ∀ x : F, ∀ u : P, (u : P ⧸ A) = ζV x → ζV (lam * x) = (h.xi u : P ⧸ A))
    (ζZ : F ≃ ↥(omega1 P))
    (hζZadd : ∀ x y : F, ζZ (x + y) = ζZ x * ζZ y)
    (hζZeq : ∀ x : F, ((ζZ (mu * x) : ↥(omega1 P)) : P) = h.xi ((ζZ x : ↥(omega1 P)) : P)) :
    False := by
  classical
  -- ## basic facts about the two identifications
  have hAne : A ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥A = 1 := by rw [hbot]; simp
    have h2 : 4 ≤ Nat.card ↥(omega1 P) := h.omega1_card_ge_four
    rw [h1] at hcard
    have h3 : 16 ≤ (Nat.card ↥(omega1 P)) ^ 2 := by nlinarith
    omega
  have hζZ0 : ζZ 0 = 1 := by
    have h1 : ζZ 0 = ζZ 0 * ζZ 0 := by
      have h2 := hζZadd 0 0
      rwa [add_zero] at h2
    exact (mul_left_cancel (show ζZ 0 * 1 = ζZ 0 * ζZ 0 by rw [mul_one]; exact h1)).symm
  have hζV0 : ζV 0 = 1 := by
    have h1 : ζV 0 = ζV 0 * ζV 0 := by
      have h2 := hζVadd 0 0
      rwa [add_zero] at h2
    exact (mul_left_cancel (show ζV 0 * 1 = ζV 0 * ζV 0 by rw [mul_one]; exact h1)).symm
  have hζV_one : ∀ x : F, ζV x = 1 ↔ x = 0 := fun x =>
    ⟨fun hx => ζV.injective (by rw [hx, hζV0]), fun hx => by rw [hx, hζV0]⟩
  -- ## the section `σ : F → P` of `ζV`
  let σ : F → P := fun x => Quotient.out (ζV x)
  have hσ : ∀ x : F, (σ x : P ⧸ A) = ζV x := fun x => QuotientGroup.out_eq' (ζV x)
  have hσadd : ∀ x y : F, ∃ t ∈ A, σ x * σ y = σ (x + y) * t := by
    intro x y
    have hq : (σ (x + y) : P ⧸ A) = (σ x * σ y : P ⧸ A) := by
      calc (σ (x + y) : P ⧸ A) = ζV (x + y) := hσ (x + y)
        _ = ζV x * ζV y := hζVadd x y
        _ = (σ x : P ⧸ A) * (σ y : P ⧸ A) := by rw [hσ x, hσ y]
        _ = (σ x * σ y : P ⧸ A) := (quot_mk_mul (σ x) (σ y)).symm
    obtain ⟨t, htA, ht⟩ := exists_mul_mem_of_quot_eq hq
    exact ⟨t⁻¹, A.inv_mem htA, by rw [ht]; group⟩
  have hσlam : ∀ x : F, ∃ t ∈ A, σ (lam * x) = h.xi (σ x) * t := by
    intro x
    refine exists_mul_mem_of_quot_eq ?_
    rw [hσ (lam * x)]
    exact hζVeq x (σ x) (hσ x)
  -- ## the section `ρ : F → A` of the squaring map
  have hρ_exists : ∀ y : F, ∃ a ∈ A, a * a = ((ζZ y : ↥(omega1 P)) : P) := by
    intro y
    have hmem : ((ζZ y : ↥(omega1 P)) : P) ∈ powSub A 2 := by
      rw [htop]; exact (ζZ y).2
    obtain ⟨a, ha, ha2⟩ := (mem_powSub_iff hAab).mp hmem
    exact ⟨a, ha, by rwa [pow_two] at ha2⟩
  let ρ : F → P := fun y => Classical.choose (hρ_exists y)
  have hρ_mem : ∀ y : F, ρ y ∈ A := fun y => (Classical.choose_spec (hρ_exists y)).1
  have hρ_sq : ∀ y : F, ρ y * ρ y = ((ζZ y : ↥(omega1 P)) : P) :=
    fun y => (Classical.choose_spec (hρ_exists y)).2
  -- `ρ` is `ξ`-equivariant modulo `A²`
  have hξρ_mem : ∀ y : F, h.xi (ρ y) ∈ A := by
    intro y
    rw [← hAxi]
    exact Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom (hρ_mem y)
  have hρω : ∀ y : F, ρ (mu * y) * (h.xi (ρ y))⁻¹ ∈ powSub A 2 := by
    intro y
    refine mul_inv_mem_powSub_two_of_sq_eq h hAab htop (hρ_mem (mu * y)) (hξρ_mem y) ?_
    rw [hρ_sq (mu * y), hζZeq y, ← map_mul, hρ_sq y]
  -- ## the four maps of the field core
  let f : F → F := fun x => ζZ.symm ⟨(σ x) ^ 4, pow4_mem h htop hsq (σ x)⟩
  have hfZ : ∀ x : F, ζZ (f x) = ⟨(σ x) ^ 4, pow4_mem h htop hsq (σ x)⟩ :=
    fun x => ζZ.apply_symm_apply _
  let β : F → F → F := fun x y => ζZ.symm ⟨⁅σ x, σ y⁆ ^ 2, comm_sq_mem h hGs htop (σ x) (σ y)⟩
  have hβZ : ∀ x y : F,
      ζZ (β x y) = ⟨⁅σ x, σ y⁆ ^ 2, comm_sq_mem h hGs htop (σ x) (σ y)⟩ :=
    fun x y => ζZ.apply_symm_apply _
  let B : F → F → F := fun x y =>
    ζZ.symm ⟨⁅σ x, ρ y⁆, bracket_mem_omega1 h hAxi hAab hGs htop (σ x) (hρ_mem y)⟩
  have hBZ : ∀ x y : F,
      ζZ (B x y) = ⟨⁅σ x, ρ y⁆, bracket_mem_omega1 h hAxi hAab hGs htop (σ x) (hρ_mem y)⟩ :=
    fun x y => ζZ.apply_symm_apply _
  -- ## biadditivity of `β`
  have hbeta1 : ∀ a b d : F, β (a + b) d = β a d + β b d := by
    intro a b d
    apply ζZ.injective
    rw [hζZadd (β a d) (β b d)]
    apply Subtype.ext
    rw [hβZ (a + b) d, hβZ a d, hβZ b d]
    change ⁅σ (a + b), σ d⁆ ^ 2 = ⁅σ a, σ d⁆ ^ 2 * ⁅σ b, σ d⁆ ^ 2
    obtain ⟨t, htA, ht⟩ := hσadd a b
    have h1 : ⁅σ (a + b), σ d⁆ ^ 2 = ⁅σ a * σ b, σ d⁆ ^ 2 := by
      have hc := comm_sq_congr h hAxi hAab hGs htop (σ (a + b)) (σ d) (b := 1) htA
        (A.one_mem)
      rw [← ht, mul_one] at hc
      exact hc.symm
    rw [h1, comm_sq_mul_left h hAxi hAab hGs htop (σ a) (σ b) (σ d)]
  have hbeta2 : ∀ a b d : F, β a (b + d) = β a b + β a d := by
    intro a b d
    apply ζZ.injective
    rw [hζZadd (β a b) (β a d)]
    apply Subtype.ext
    rw [hβZ a (b + d), hβZ a b, hβZ a d]
    change ⁅σ a, σ (b + d)⁆ ^ 2 = ⁅σ a, σ b⁆ ^ 2 * ⁅σ a, σ d⁆ ^ 2
    obtain ⟨t, htA, ht⟩ := hσadd b d
    have h1 : ⁅σ a, σ (b + d)⁆ ^ 2 = ⁅σ a, σ b * σ d⁆ ^ 2 := by
      have hc := comm_sq_congr h hAxi hAab hGs htop (σ a) (σ (b + d)) (a := 1) (b := t)
        (A.one_mem) htA
      rw [mul_one, ← ht] at hc
      exact hc.symm
    rw [h1, comm_sq_mul_right h hAab hGs htop (σ a) (σ b) (σ d)]
  -- ## `ξ`-equivariance of `β`
  have hbetaeq : ∀ a b : F, β (lam * a) (lam * b) = mu * β a b := by
    intro a b
    obtain ⟨c, hcA, hc⟩ := hσlam a
    obtain ⟨e, heA, he⟩ := hσlam b
    apply ζZ.injective
    apply Subtype.ext
    rw [hζZeq (β a b), hβZ a b, hβZ (lam * a) (lam * b)]
    change ⁅σ (lam * a), σ (lam * b)⁆ ^ 2 = h.xi (⁅σ a, σ b⁆ ^ 2)
    rw [hc, he, comm_sq_congr h hAxi hAab hGs htop (h.xi (σ a)) (h.xi (σ b)) hcA heA,
      ← map_commutatorElement, ← map_pow]
  -- ## `β` is alternating
  have hbetaalt : ∀ a : F, β a a = 0 := by
    intro a
    have h1 : ζZ (β a a) = ζZ 0 := by
      rw [hζZ0, hβZ a a]
      apply Subtype.ext
      change ⁅σ a, σ a⁆ ^ 2 = (1 : P)
      rw [show ⁅σ a, σ a⁆ = 1 from by rw [commutatorElement_def]; group, one_pow]
    exact ζZ.injective h1
  -- ## `β` does not vanish
  have hbetane : ∃ a b : F, β a b ≠ 0 := by
    obtain ⟨u, v, huv⟩ := aux_beta_ne h hGs htop hcard
    refine ⟨ζV.symm (u : P ⧸ A), ζV.symm (v : P ⧸ A), ?_⟩
    intro h0
    have hσu : (σ (ζV.symm (u : P ⧸ A)) : P ⧸ A) = (u : P ⧸ A) := by
      rw [hσ]; simp
    have hσv : (σ (ζV.symm (v : P ⧸ A)) : P ⧸ A) = (v : P ⧸ A) := by
      rw [hσ]; simp
    obtain ⟨s, hsA, hs⟩ := exists_mul_mem_of_quot_eq hσu
    obtain ⟨t, htA, ht⟩ := exists_mul_mem_of_quot_eq hσv
    have h1 : ζZ (β (ζV.symm (u : P ⧸ A)) (ζV.symm (v : P ⧸ A))) = 1 := by rw [h0, hζZ0]
    rw [hβZ] at h1
    have h2 : ⁅σ (ζV.symm (u : P ⧸ A)), σ (ζV.symm (v : P ⧸ A))⁆ ^ 2 = 1 :=
      congrArg (fun z : ↥(omega1 P) => (z : P)) h1
    rw [hs, ht, comm_sq_congr h hAxi hAab hGs htop u v hsA htA] at h2
    exact huv (by rw [htop]; exact h.mem_omega1.mpr h2)
  -- ## biadditivity of `B`
  have hB1 : ∀ a b d : F, B (a + b) d = B a d + B b d := by
    intro a b d
    apply ζZ.injective
    rw [hζZadd (B a d) (B b d)]
    apply Subtype.ext
    rw [hBZ (a + b) d, hBZ a d, hBZ b d]
    change ⁅σ (a + b), ρ d⁆ = ⁅σ a, ρ d⁆ * ⁅σ b, ρ d⁆
    obtain ⟨t, htA, ht⟩ := hσadd a b
    have h1 : ⁅σ (a + b), ρ d⁆ = ⁅σ a * σ b, ρ d⁆ := by
      have hc := bracket_mul_left_exact h hAab (σ (a + b)) (hρ_mem d) htA
      rw [← ht] at hc
      exact hc.symm
    rw [h1, bracket_mul_omega h hAxi hAab hGs htop (σ a) (σ b) (hρ_mem d)]
  have hB2 : ∀ a b d : F, B a (b + d) = B a b + B a d := by
    intro a b d
    have hsqeq : ρ (b + d) * ρ (b + d) = (ρ b * ρ d) * (ρ b * ρ d) := by
      rw [hρ_sq (b + d), hζZadd,
        show (ρ b * ρ d) * (ρ b * ρ d) = (ρ b * ρ b) * (ρ d * ρ d) from by
          rw [show (ρ b * ρ d) * (ρ b * ρ d) = ρ b * (ρ d * ρ b) * ρ d from by group,
            hAab (ρ d) (hρ_mem d) (ρ b) (hρ_mem b)]
          group]
      rw [hρ_sq b, hρ_sq d]
      rfl
    obtain ⟨z, hzA, hz2⟩ := (mem_powSub_iff hAab).mp
      (mul_inv_mem_powSub_two_of_sq_eq h hAab htop (hρ_mem (b + d))
        (A.mul_mem (hρ_mem b) (hρ_mem d)) hsqeq)
    have hzeq : ρ (b + d) = (ρ b * ρ d) * z ^ 2 := by
      have key : (ρ b * ρ d) * z ^ 2 = ρ (b + d) := by
        rw [hz2]
        have hcomm := hAab (ρ b * ρ d) (A.mul_mem (hρ_mem b) (hρ_mem d)) (ρ (b + d))
          (hρ_mem (b + d))
        calc (ρ b * ρ d) * (ρ (b + d) * (ρ b * ρ d)⁻¹)
            = ((ρ b * ρ d) * ρ (b + d)) * (ρ b * ρ d)⁻¹ := by group
          _ = (ρ (b + d) * (ρ b * ρ d)) * (ρ b * ρ d)⁻¹ := by rw [hcomm]
          _ = ρ (b + d) := by group
      exact key.symm
    apply ζZ.injective
    rw [hζZadd (B a b) (B a d)]
    apply Subtype.ext
    rw [hBZ a (b + d), hBZ a b, hBZ a d]
    change ⁅σ a, ρ (b + d)⁆ = ⁅σ a, ρ b⁆ * ⁅σ a, ρ d⁆
    rw [hzeq, bracket_mul_central h hAab hGs htop (σ a) (A.mul_mem (hρ_mem b) (hρ_mem d))
        (pow_mem_powSub (n := 2) hzA),
      bracket_mul_exact h hAab hGs (σ a) (hρ_mem b) (hρ_mem d)]
  -- ## `ξ`-equivariance of `B`
  have hBeq : ∀ a b : F, B (lam * a) (mu * b) = mu * B a b := by
    intro a b
    obtain ⟨c, hcA, hc⟩ := hσlam a
    obtain ⟨z, hzA, hz2⟩ := (mem_powSub_iff hAab).mp (hρω b)
    have hzeq : ρ (mu * b) = h.xi (ρ b) * z ^ 2 := by
      have key : h.xi (ρ b) * z ^ 2 = ρ (mu * b) := by
        rw [hz2]
        have hcomm := hAab (ρ (mu * b)) (hρ_mem (mu * b)) (h.xi (ρ b)) (hξρ_mem b)
        calc h.xi (ρ b) * (ρ (mu * b) * (h.xi (ρ b))⁻¹)
            = (h.xi (ρ b) * ρ (mu * b)) * (h.xi (ρ b))⁻¹ := by group
          _ = (ρ (mu * b) * h.xi (ρ b)) * (h.xi (ρ b))⁻¹ := by rw [hcomm]
          _ = ρ (mu * b) := by group
      exact key.symm
    apply ζZ.injective
    apply Subtype.ext
    rw [hζZeq (B a b), hBZ a b, hBZ (lam * a) (mu * b)]
    change ⁅σ (lam * a), ρ (mu * b)⁆ = h.xi (⁅σ a, ρ b⁆)
    rw [hc, bracket_mul_left_exact h hAab (h.xi (σ a)) (hρ_mem (mu * b)) hcA, hzeq,
      bracket_mul_central h hAab hGs htop (h.xi (σ a)) (hξρ_mem b) (pow_mem_powSub (n := 2) hzA),
      ← map_commutatorElement]
  -- ## non-vanishing of `B`
  have hBne : ∃ a b : F, B a b ≠ 0 := by
    have hAne_top : A ≠ ⊤ := by
      intro hAtop
      obtain ⟨x, y, hxy⟩ := h.noncomm
      exact hxy (hAab x (by rw [hAtop]; trivial) y (by rw [hAtop]; trivial))
    obtain ⟨u, huA⟩ : ∃ u : P, u ∉ A := by
      by_contra hcon
      push Not at hcon
      exact hAne_top (le_antisymm le_top (fun x _ => hcon x))
    obtain ⟨a, haA, ha1⟩ := hcent u huA
    have ha2 : a ^ 2 ∈ omega1 P := by
      rw [← htop]; exact pow_mem_powSub (n := 2) haA
    set b : F := ζZ.symm ⟨a ^ 2, ha2⟩ with hbdef
    have hbZ : ζZ b = ⟨a ^ 2, ha2⟩ := ζZ.apply_symm_apply _
    refine ⟨ζV.symm (u : P ⧸ A), b, ?_⟩
    intro h0
    have hρa : ρ b * a⁻¹ ∈ powSub A 2 := by
      refine mul_inv_mem_powSub_two_of_sq_eq h hAab htop (hρ_mem b) haA ?_
      rw [hρ_sq, hbZ]
      change a ^ 2 = a * a
      rw [pow_two]
    obtain ⟨w, hwA, hw2⟩ := (mem_powSub_iff hAab).mp hρa
    have hweq : ρ b = a * w ^ 2 := by
      have key : a * w ^ 2 = ρ b := by
        rw [hw2]
        calc a * (ρ b * a⁻¹) = (a * ρ b) * a⁻¹ := by group
          _ = (ρ b * a) * a⁻¹ := by rw [hAab a haA (ρ b) (hρ_mem b)]
          _ = ρ b := by group
      exact key.symm
    have hσu : (σ (ζV.symm (u : P ⧸ A)) : P ⧸ A) = (u : P ⧸ A) := by rw [hσ]; simp
    obtain ⟨s, hsA, hs⟩ := exists_mul_mem_of_quot_eq hσu
    have h2 : ⁅σ (ζV.symm (u : P ⧸ A)), ρ b⁆ = 1 := by
      have h1 : ζZ (B (ζV.symm (u : P ⧸ A)) b) = 1 := by rw [h0, hζZ0]
      rw [hBZ] at h1
      exact congrArg (fun z : ↥(omega1 P) => (z : P)) h1
    rw [hweq, bracket_mul_central h hAab hGs htop (σ (ζV.symm (u : P ⧸ A))) haA
        (pow_mem_powSub (n := 2) hwA),
      hs, bracket_mul_left_exact h hAab u haA hsA] at h2
    exact ha1 h2
  -- ## the quadratic relation
  have hBquad : ∀ a : F, B a (f a) = 0 := by
    intro a
    have hρfa : ρ (f a) * ((σ a) ^ 2)⁻¹ ∈ powSub A 2 := by
      refine mul_inv_mem_powSub_two_of_sq_eq h hAab htop (hρ_mem (f a))
        (hsq (σ a)) ?_
      rw [hρ_sq, hfZ]
      change (σ a) ^ 4 = (σ a) ^ 2 * (σ a) ^ 2
      rw [← pow_add]
    obtain ⟨z, hzA, hz2⟩ := (mem_powSub_iff hAab).mp hρfa
    have hzeq : ρ (f a) = (σ a) ^ 2 * z ^ 2 := by
      have key : (σ a) ^ 2 * z ^ 2 = ρ (f a) := by
        rw [hz2]
        have hcomm := hAab ((σ a) ^ 2) (hsq (σ a)) (ρ (f a))
          (hρ_mem (f a))
        calc (σ a) ^ 2 * (ρ (f a) * ((σ a) ^ 2)⁻¹)
            = ((σ a) ^ 2 * ρ (f a)) * ((σ a) ^ 2)⁻¹ := by group
          _ = (ρ (f a) * (σ a) ^ 2) * ((σ a) ^ 2)⁻¹ := by rw [hcomm]
          _ = ρ (f a) := by group
      exact key.symm
    apply ζZ.injective
    rw [hζZ0]
    apply Subtype.ext
    rw [hBZ a (f a)]
    change ⁅σ a, ρ (f a)⁆ = (1 : P)
    rw [hzeq, bracket_mul_central h hAab hGs htop (σ a)
        (hsq (σ a)) (pow_mem_powSub (n := 2) hzA)]
    exact show ⁅σ a, (σ a) ^ 2⁆ = (1 : P) from by
      rw [show ⁅σ a, (σ a) ^ 2⁆ = 1 from by rw [pow_two, commutatorElement_def]; group]
    -- ## injectivity of `f`
  -- transitivity of the `ξ`-action on the non-trivial elements of `P / A`
  have hζpow : ∀ {u : P} {x : F}, (u : P ⧸ A) = ζV x → ∀ s : ℕ,
      ζV (lam ^ s * x) = ((h.xi ^ s) u : P ⧸ A) := by
    intro u x hu s
    induction s with
    | zero => simpa using hu.symm
    | succ s ih =>
      have h2 := hζVeq (lam ^ s * x) ((h.xi ^ s) u) ih.symm
      rw [show lam * (lam ^ s * x) = lam ^ (s + 1) * x from by
        rw [← mul_assoc, ← pow_succ']] at h2
      rw [show h.xi ((h.xi ^ s) u) = (h.xi ^ (s + 1)) u from by
        rw [pow_succ', MulAut.mul_apply]] at h2
      exact h2
  have htrans : ∀ u v : P, u ∉ A → v ∉ A → ∃ s : ℕ, v⁻¹ * ((h.xi ^ s) u) ∈ A := by
    intro u v hu hv
    have hx : ζV.symm (u : P ⧸ A) ≠ 0 := by
      intro h0
      have h1 : (u : P ⧸ A) = 1 := by
        rw [← ζV.apply_symm_apply (u : P ⧸ A), h0, hζV0]
      exact hu ((QuotientGroup.eq_one_iff u).mp h1)
    have hy : ζV.symm (v : P ⧸ A) ≠ 0 := by
      intro h0
      have h1 : (v : P ⧸ A) = 1 := by
        rw [← ζV.apply_symm_apply (v : P ⧸ A), h0, hζV0]
      exact hv ((QuotientGroup.eq_one_iff v).mp h1)
    have hlamord' : orderOf lam = Fintype.card F - 1 := by rw [hFcard]; exact hlamord
    obtain ⟨s, hs⟩ := pow_exhaust_of_orderOf_card hlamord'
      (x := ζV.symm (v : P ⧸ A) * (ζV.symm (u : P ⧸ A))⁻¹)
      (mul_ne_zero hy (inv_ne_zero hx))
    refine ⟨s, ?_⟩
    have hX : lam ^ s * ζV.symm (u : P ⧸ A) = ζV.symm (v : P ⧸ A) := by
      rw [hs]
      first
        | rw [mul_assoc, inv_mul_cancel, mul_one]
        | rw [mul_assoc, zpow_neg_one, inv_mul_cancel, mul_one]
        | field_simp
        | group
    have hkey : ζV (lam ^ s * ζV.symm (u : P ⧸ A)) = (v : P ⧸ A) := by
      rw [hX, ζV.apply_symm_apply]
    have h2 := hζpow (u := u) (x := ζV.symm (u : P ⧸ A))
      (by rw [ζV.apply_symm_apply]) s
    rw [hkey] at h2
    exact QuotientGroup.eq.mp h2
  -- every element outside `A` squares into `A ^ 2` as soon as one does, by transitivity
  have hA2inv_pow : ∀ s : ℕ,
      (powSub A 2).map ((h.xi ^ s : MulAut P)).toMonoidHom = powSub A 2 := by
    intro s
    induction s with
    | zero => rw [pow_zero]; exact Subgroup.map_id _
    | succ s ih =>
      rw [pow_succ]
      rw [show (((h.xi ^ s) * h.xi : MulAut P)).toMonoidHom
          = ((h.xi ^ s : MulAut P)).toMonoidHom.comp (h.xi : MulAut P).toMonoidHom from by
        ext x; simp [MulAut.mul_apply]]
      rw [← Subgroup.map_map, map_powSub (h.xi : MulAut P) hAxi 2, ih]
  have hfinj : ∀ a : F, f a = 0 → a = 0 := by
    intro a ha
    have h1 : ζZ (f a) = 1 := by rw [ha, hζZ0]
    rw [hfZ] at h1
    have h2 : (σ a) ^ 4 = 1 := congrArg (fun z : ↥(omega1 P) => (z : P)) h1
    have h3 : (σ a) ^ 2 ∈ powSub A 2 := by
      have h4 : ((σ a) ^ 2) ^ 2 = 1 := by rw [← pow_mul, show 2 * 2 = 4 from rfl]; exact h2
      rw [htop]
      exact h.mem_omega1.mpr h4
    by_contra ha0
    have hσaA : σ a ∉ A := by
      intro hmem
      have hcos : (σ a : P ⧸ A) = 1 := (QuotientGroup.eq_one_iff (σ a)).mpr hmem
      rw [hσ a] at hcos
      exact ha0 ((hζV_one a).mp hcos)
    -- then all squares of `P` lie in `A ^ 2`
    have hsq2 : ∀ x : P, x ^ 2 ∈ powSub A 2 := by
      intro x
      by_cases hx : x ∈ A
      · exact pow_mem_powSub (n := 2) hx
      · obtain ⟨s, hs⟩ := htrans (σ a) x hσaA hx
        obtain ⟨c, hcA, hc⟩ := exists_mul_mem_of_quot_eq (QuotientGroup.eq.mpr hs)
        set w : P := (h.xi ^ s) (σ a) with hwdef
        have h4 : w ^ 2 ∈ powSub A 2 := by
          have h5 : w ^ 2 = (h.xi ^ s) ((σ a) ^ 2) := by rw [hwdef, map_pow]
          rw [h5, ← hA2inv_pow s]
          exact Subgroup.mem_map_of_mem ((h.xi ^ s : MulAut P).toMonoidHom) h3
        have h6 : (w * c) * (w * c) * (w * w)⁻¹ ∈ powSub A 2 :=
          nsd_coset_sq_wd h hAxi hAab hGs hsq w hcA
        have h7 : x * x ∈ powSub A 2 := by
          have h8 : x * x = (w * c) * (w * c) := by rw [hc]
          rw [h8]
          have h9 : (w * c) * (w * c) = ((w * c) * (w * c) * (w * w)⁻¹) * (w * w) := by group
          rw [h9]
          exact Subgroup.mul_mem _ h6 (by rw [← pow_two]; exact h4)
        rw [pow_two]
        exact h7
    -- hence `A = P' ⊆ A ^ 2`
    have hcomm : ∀ u v : P, ⁅u, v⁆ ∈ powSub A 2 :=
      fun u v => comm_mem_powSub_two_of_sq_mem h hAxi hAab hGs hsq2 u v
    have hAle : A ≤ powSub A 2 := by
      have h : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ powSub A 2 := by
        rw [Subgroup.commutator_le]
        intro u _ v _
        exact hcomm u v
      rwa [hGs] at h
    have hAeq : A = powSub A 2 := le_antisymm hAle (powSub_le (n := 2) (by norm_num))
    have hcard' : (2 : ℕ) ^ n = 2 ^ n * 2 ^ n := by
      have h11 : Nat.card ↥A = Nat.card ↥(powSub A 2) :=
        congrArg (fun H : Subgroup P => Nat.card ↥H) hAeq
      have h12 : Nat.card ↥(powSub A 2) = 2 ^ n := by rw [htop, hZcard]
      have h13 : Nat.card ↥A = 2 ^ n * 2 ^ n := by rw [hcard, hZcard, sq]
      rw [h11, h12] at h13
      exact h13
    have h4 : 4 ≤ 2 ^ n := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    nlinarith [hcard', h4]
  -- ## the hypothesis `lam ≠ mu` of the field core
  have hlam0 : lam ≠ 0 := by
    intro h0
    rw [h0, orderOf_zero] at hlamord
    have h4 : 4 ≤ 2 ^ n := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hmu0 : mu ≠ 0 := by
    intro h0
    rw [h0, orderOf_zero] at hmuord
    have h4 : 4 ≤ 2 ^ n := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hlamu : lam ≠ mu :=
    c4_lam_ne_mu hn hFcard lam mu hlamord hmuord β hbeta1 hbeta2 hbetaalt hbetaeq hbetane
  exact c4_field_core n hn hFcard lam mu hlam0 hmu0 hlamu hlamord hmuord β f B
    hbeta1 hbeta2 hbetaeq hbetaalt hbetane hfinj hB1 hB2 hBeq hBne hBquad

/-- **Sub-case 1 of the `C₄` exclusion** (Higman's Lemma 8 applied with `C = ⊤`, whose proof
goes through Lemma 6).  In the `C₄` case, if `P / A` is irreducible as an `𝔽₂[ξ]`-module —
i.e. there is no normal `ξ`-invariant subgroup strictly between `A` and `P` — then we reach a
contradiction.

Reason: with `C = ⊤` the hypothesis `C' = A` holds by `hGs`, so Higman's Lemma 8
(`Work.Higman.higman_lemma8_new`, in `Submission/Work/Higman/higman_lemma8_new.lean`) gives
`exp A ≤ 2`, i.e. every element of `A` is an involution; with `hNA` this gives `A = Ω₁(P)`,
so `A ^ (2) = ⊥` while `A ^ (2) = Ω₁(P)` has order `≥ 4` by `htop` and
`IsSuzuki2Grp.omega1_card_ge_four`. -/
theorem nsd_false_of_irreducible {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hirr : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D = A ∨ D = ⊤) :
    False := by
  classical
  have hAn : A.Normal := nsd_normal hGs
  haveI : A.Normal := hAn
  -- ## the centraliser of `A`
  have hAleD : A ≤ Subgroup.centralizer (A : Set P) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hAab b hb a ha
  have hDinv : (Subgroup.centralizer (A : Set P)).map (h.xi : MulAut P).toMonoidHom
      = Subgroup.centralizer (A : Set P) := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩ a ha
      rw [Subgroup.mem_centralizer_iff] at hy
      have ha' : ((h.xi : MulAut P)⁻¹) a ∈ A := symm_mem_of_map_eq (h.xi : MulAut P) hAxi ha
      have h1 : ((h.xi : MulAut P)⁻¹) a * y = y * ((h.xi : MulAut P)⁻¹) a := hy _ ha'
      calc a * h.xi y = h.xi (((h.xi : MulAut P)⁻¹) a) * h.xi y := by simp
        _ = h.xi (((h.xi : MulAut P)⁻¹) a * y) := by rw [map_mul]
        _ = h.xi (y * ((h.xi : MulAut P)⁻¹) a) := by rw [h1]
        _ = h.xi y * a := by rw [map_mul]; simp
    · intro hx
      refine ⟨((h.xi : MulAut P)⁻¹) x, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro a ha
      have ha' : (h.xi : MulAut P) a ∈ A := by
        rw [← hAxi]
        exact Subgroup.mem_map_of_mem _ ha
      have h1 : h.xi a * x = x * h.xi a := hx _ ha'
      have h2 := congrArg (fun t : P => ((h.xi : MulAut P)⁻¹) t) h1
      simpa using h2
  -- ## every element outside `A` fails to centralise `A`
  have hcent : ∀ u : P, u ∉ A → ∃ a ∈ A, ⁅u, a⁆ ≠ 1 := by
    rcases hirr (Subgroup.centralizer (A : Set P)) inferInstance hDinv hAleD with hDA | hDtop
    · intro u hu
      by_contra hcon
      push Not at hcon
      have huD : u ∈ Subgroup.centralizer (A : Set P) := by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact (commutatorElement_eq_one_iff_mul_comm.mp (hcon a ha)).symm
      rw [hDA] at huD
      exact hu huD
    · intro u hu
      exfalso
      have hAZ : A ≤ Subgroup.center P := (Subgroup.centralizer_eq_top_iff_subset).mp hDtop
      have hZc : Subgroup.center P = omega1 P := center_eq_omega1_new h
      have hAle2 : A ≤ powSub A 2 := by
        rw [htop]
        intro a ha
        rw [← hZc]
        exact hAZ ha
      have hAeq : A = powSub A 2 := le_antisymm hAle2 (powSub_le (n := 2) (by norm_num))
      have hcard2 : Nat.card ↥(omega1 P) = (Nat.card ↥(omega1 P)) ^ 2 := by
        have h1 : Nat.card ↥A = Nat.card ↥(omega1 P) := by rw [hAeq, htop]
        rw [← h1, h1] at hcard
        exact hcard
      nlinarith [hcard2, h.omega1_card_ge_four]
  -- ## the two fields
  have hAne : A ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥A = 1 := by rw [hbot]; simp
    rw [h1] at hcard
    have h4 : 4 ≤ Nat.card ↥(omega1 P) := h.omega1_card_ge_four
    nlinarith [hcard, h4]
  obtain ⟨nZ, FZ, hFZf, hFZft, hFZd, hFZc, mu, hFZcard, hnZ, hmuord, hmu0, ζZ,
    hζZadd, hζZeq⟩ := omega1_iso_field h
  have hZcard : Nat.card ↥(omega1 P) = 2 ^ nZ := by
    rw [← Nat.card_congr ζZ, Nat.card_eq_fintype_card, hFZcard]
  obtain ⟨FV, hFVf, hFVft, hFVd, hFVc, lamV, hFVcard, hnV, hlamVord, hlamV0, ζV,
    hζVadd, hζVeq⟩ :=
    L1_iso_field_exp h hAxi hAab hNA hGs hsq hA4 htop hcard hirr nZ hZcard
  have hcFVZ : Fintype.card FV = Fintype.card FZ := by rw [hFVcard, hFZcard]
  let σ : FV ≃+* FZ := FiniteField.ringEquivOfCardEq hcFVZ
  set lam : FZ := σ lamV with hlamdef
  have hlamord : orderOf lam = 2 ^ nZ - 1 := by
    rw [hlamdef]
    have key : orderOf ((σ : FV →* FZ) lamV) = orderOf lamV :=
      orderOf_injective (σ : FV →* FZ) σ.injective lamV
    have h1 : orderOf (σ lamV) = orderOf ((σ : FV →* FZ) lamV) := rfl
    rw [h1, key, hlamVord]
  let ζV' : FZ ≃ (P ⧸ A) := σ.symm.toEquiv.trans ζV
  have hζV'add : ∀ x y : FZ, ζV' (x + y) = ζV' x * ζV' y := by
    intro x y
    show ζV (σ.symm (x + y)) = ζV (σ.symm x) * ζV (σ.symm y)
    rw [map_add, hζVadd]
  have hζV'eq : ∀ x : FZ, ∀ u : P, (u : P ⧸ A) = ζV' x →
      ζV' (lam * x) = (h.xi u : P ⧸ A) := by
    intro x u hu
    show ζV (σ.symm (lam * x)) = (h.xi u : P ⧸ A)
    have h1 : σ.symm (lam * x) = lamV * σ.symm x := by
      rw [hlamdef, map_mul, σ.symm_apply_apply]
    rw [h1]
    exact hζVeq (σ.symm x) u hu
  exact nsd_core h hAxi hAab hNA hGs hsq hA4 htop hcard hcent hnZ hFZcard hZcard
    lam mu hlamord hmuord ζV' hζV'add hζV'eq ζZ hζZadd hζZeq

end Work.Higman.H8.Clean
