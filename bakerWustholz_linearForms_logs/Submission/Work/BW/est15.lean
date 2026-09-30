import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.est15defs
import Submission.Work.BW.phi_gKJ_eq_acg
import Submission.Work.BW.split_aux
import Submission.Work.BW.num_est15_arch2
import Submission.Work.BW.num_card_AuxIdx
import Submission.Work.BW.coefPart_log_finite_le
import Submission.Work.BW.est15_pi_bound
import Submission.Work.BW.est15_coefKJ_infl
import Submission.Work.BW.est15_coefKJ_fin
import Submission.Work.BW.est15_place_inf
import Submission.Work.BW.est15_place_fin
import Submission.Work.BW.est15_height_id
import Submission.Work.BW.est15_kummer_sum
import Submission.Work.BW.est15_bracket
import Submission.Work.BW.est15_mon1
import Submission.Work.BW.est15_mon_bound
import Submission.Work.BW.est15_arith_core
import Submission.Work.BW.est15_final_arith
import Submission.Work.BW.sum_gamInt_le
import Submission.Work.BW.thetaRatQ_log_le
import Submission.Work.BW.num_est15_slacks
import Submission.Work.BW.LiouvilleAux.product_formula_isolate
import Submission.Work.BW.LiouvilleAux.sum_mult_erase
import Submission.Work.BW.prod_formula_log
import Submission.Work.BW.num_kum
import Submission.Work.BW.acH_lower
import Submission.Work.BW.sigma_ge
import Submission.Work.BW.num_T
import Submission.Work.BW.num_D_lower
import Submission.Work.BW.one_le_pDj
import Submission.Work.BW.pD0_succ_mul_log_le
import Submission.Work.BW.ulcm_le_three_pow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
Guidance from the project lead (the requester): BW (15) at level `J` — `est15` below.

# Proof plan (BW §15, p. 44–45; level-`J` version p. 58)

The statement is BW's Liouville-type lower bound for `g^{(J)}(s;t) = acg φ α b k L ι v σ p J μ t0 t s`.

**Putting `x ∈ K`.** `Submission.Work.BW.est15defs` defines the explicit element
`gKJ b k L ι α' h D0 Dj p J μ t0 t s ∈ K`, whose `λ`-summand is `p λ * coefKJ … λ` with
`coefKJ = coefPart * ∏_j (α' j)^{s⌊λ_j/2^J⌋}`, `coefPart = (piRat:K) * ((ulcm h):K)^t0 * (thetaJ:K)`
(`piRat = ∏_m Δ(γ_m(λ);t_m)` at `γ_m(λ) = gamInt b k L (ι m) λ ∈ ℤ`, and
`thetaJ = Θ(s/2^J + λ₋₁; h, λ₀+1, t₀) ∈ ℚ`).  The algebraic identity
`φ (gKJ …) = acg … (s:ℂ)` is **`Work.BW.phi_gKJ_eq_acg`** (proved, file
`Submission/Work/BW/phi_gKJ_eq_acg.lean`).

**Product formula.** With `hg`, `x ≠ 0`; `v₀ := InfinitePlace.mk φ` satisfies `v₀ x = ‖acg …‖`,
and `LiouvilleAux.product_formula_isolate` gives
`m₀ log(v₀ x) = -(∑_{w ≠ v₀} mult_w log(w x) + ∑ᶠ_w log(w x))`, `m₀ = v₀.mult`.

**Per-place bounds.** For every `λ` and every place `w ≠ v₀`:
* `log(w x) ≤ log(⨆_λ w (p λ)) + log(⨆_λ w (coefKJ λ))` (+ `log N` at infinite places,
  `N = Fintype.card (AuxIdx …)`), because `|x|_w ≤ N · max_λ |p λ|_w · max_λ |coefKJ λ|_w`.
* Infinite `w`: `log(w (coefPart λ)) ≤
    T'(1 + log(1 + gamBound/T')) + t₀ log u(h) + (λ₀+1)h(1 + log μ + 1/μ) + (λ₀+1)|z|/μ`
  with `T' = ∑ t_m`, `μ = 57rd`, `z = 2^{-J}s + λ₋₁`; the `Π`-part is
  `log_prod_Delta_le` + `sum_gamInt_le` (`Λ ≤ gamBound K b v σ`), the `Θ`-part is
  `thetaRatQ_log_le`.
* Finite `w`: `log(w (coefPart λ)) ≤ 2Jh(λ₀+1)·(-log(w 2))` — the Kummer/2-adic integrality
  `Work.BW.coefPart_log_finite_le` (from `tijdeman_rat` and the integrality of `deltaRat`/`ulcm`).
  Summing over the finite places with the product formula for the `α'`-monomials gives
  `≤ 2Jh(D₀+1)·d·log 2 + (|s|/2^J) ∑_j D_j logHeight₁(α'_j)`.

**Height identity.** `∑_{w ≠ v₀} mult_w log(⨆_λ w (p λ)) = logHeight p - m₀ · lnp φ p`, from
`Height.logHeight_eq_log_mulHeight`, `Height.mulHeight_eq`, `NumberField.prod_archAbsVal_eq`,
`NumberField.prod_nonarchAbsVal_eq` and `InfinitePlace.apply`.

**Numerics.** `Work.BW.num_card_AuxIdx` (`log N ≤ 0.001·S·D/d`), `Work.BW.num_est15_slacks`
(`σ_j D_j d ≤ D`, `∑_j D_j logHeight₁(α'_j) ≤ D`, `(D₀+1) ≤ 0.007 D (57rd)/d`,
`2Jh(D₀+1)d log 2 ≤ kumJ`), and `Work.BW.num_est15_arch2` (the weighted Archimedean accounting,
with the factor `(d - m₀)`; note that for `d = 1` there are no Archimedean places other than `v₀`).

Combining: `log‖g^{(J)}(s)‖ ≥ lnp - h(p) - (1-1/d)(dhT* + 0.204SD) - 1.007·2^{-J}|s|D - kumJ`;
the per-place allowances sum as `0.018 + 0.075 + 0.1 + 0.001 ≤ 0.204` (in the units of `S·D/d`),
with the `|s|`-part `(1 + 0.007) ≤ 1.007`.
-/

namespace Work.BW

/-- BW (15) at level `J` (Liouville via the product formula over `K`; p. 44–45, p. 58 "(15) remains valid with |s| replaced by 2^{-J}|s| and an extra Kummer contribution"): for an integer `s` with `g^{(J)}(s) ≠ 0`, `log|g(s)| − ln(p) ≥ −{h(p) + (1−1/d)(dhT* + 0·204SD) + 1·007·2^{-J}|s|D + kum_J}`. Uses `Qdesc_val_mem`, `NumberField.prod_abs_eq_one`-type product formula, `num_kum`. -/
theorem est15 {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (μ : Fin r → ℕ) (Tst : ℝ) (hTst : Tst ≤ acT K σ) (t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (ht : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ Tst) (s : ℤ)
    (hg : acg φ α b k L ι v σ p J μ t0 t (s : ℂ) ≠ 0) :
    Real.exp (lnp φ p - (Height.logHeight p + (1 - 1 / (dK K : ℝ)) * ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ)
        + 1.007 * (((|s| : ℤ) : ℝ) / 2 ^ J) * acD K σ + kumJ K b v σ J)) ≤ ‖acg φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ := by
  classical
  have hr : 2 ≤ r := H.hr
  have hd1 : 1 ≤ dK K := Module.finrank_pos
  have hdR : (0 : ℝ) < (dK K : ℝ) := by exact_mod_cast hd1
  have hσ : ∀ j : Fin r, 1 / (dK K : ℝ) ≤ σ j := fun j => sigma_ge H j
  have hσpos : ∀ j : Fin r, 0 < σ j := fun j => lt_of_lt_of_le (by positivity) (hσ j)
  have hhnn : (0 : ℝ) ≤ (acH K b v : ℝ) := by positivity
  obtain ⟨-, -, hα'ne, -, -, -, -, -⟩ := H.hBH
  obtain ⟨hsl1, hsl2, hsl3, hsl4⟩ := num_est15_slacks H J
  have hX : gKJ b k L ι α' (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J μ t0 t s ≠ 0 := by
    intro h0
    exact hg (by rw [← phi_gKJ_eq_acg H J μ t0 t s, h0, map_zero])
  have hp0 : p ≠ 0 := by
    intro hp
    exact hX (by simp [gKJ, hp])
  set X : K := gKJ b k L ι α' (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J μ t0 t s with hXdef
  set m₀ : ℝ := ((NumberField.InfinitePlace.mk φ).mult : ℝ) with hm₀
  set NN : ℝ := ((Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) : ℕ) : ℝ) with hNN
  set β : Fin r → K := fun j => estBeta s (α' j) with hβdef
  set Mon : NumberField.InfinitePlace K → ℝ := fun w => estMon K σ β J s w with hMon
  set Monf : NumberField.FinitePlace K → ℝ := fun w => estMon K σ β J s w with hMonf
  set Bfin : NumberField.FinitePlace K → ℝ := fun w => estCf K b v σ J w with hBfin
  have hm1 : (1 : ℝ) ≤ m₀ := by
    rw [hm₀]
    have : 1 ≤ (NumberField.InfinitePlace.mk φ).mult := NumberField.InfinitePlace.mult_pos
    exact_mod_cast this
  have hmpos : (0 : ℝ) < m₀ := lt_of_lt_of_le one_pos hm1
  have hm0ne : m₀ ≠ 0 := hmpos.ne'
  have hmd : m₀ ≤ (dK K : ℝ) := by
    rw [hm₀, dK]
    have hsum : (∑ w : NumberField.InfinitePlace K, w.mult) = Module.finrank ℚ K :=
      NumberField.InfinitePlace.sum_mult_eq
    have hle : (NumberField.InfinitePlace.mk φ).mult ≤ ∑ w : NumberField.InfinitePlace K, w.mult :=
      Finset.single_le_sum (fun w _ => Nat.zero_le _) (Finset.mem_univ _)
    rw [hsum] at hle
    exact_mod_cast hle
  have hlogh : 0 ≤ Height.logHeight p := Height.logHeight_nonneg p
  have htT : estTp t + (t0 : ℝ) ≤ Tst := by
    have h1 : estTp t + (t0 : ℝ) = ((t0 + ∑ m, t m : ℕ) : ℝ) := by
      rw [show estTp t = (((∑ m : Fin (r - 1), t m) : ℕ) : ℝ) by simp [estTp]]
      push_cast
      ring
    rw [h1]
    exact ht
  have hLNN0 : 0 ≤ Real.log NN := by
    rw [hNN]
    by_cases hc : Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) = 0
    · rw [hc]; simp
    · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hc)
  have hLNN : Real.log NN ≤ 0.001 * acS K r b v * acD K σ / (dK K : ℝ) := by
    rw [hNN]
    exact num_card_AuxIdx H
  have hβne : ∀ j : Fin r, β j ≠ 0 := by
    intro j
    have hbj : β j = (if 0 ≤ s then α' j else (α' j)⁻¹) := rfl
    rw [hbj]
    split_ifs with hs
    · exact (hα'ne j).1
    · exact inv_ne_zero (hα'ne j).1
  have hβlog : ∀ j : Fin r, Height.logHeight₁ (β j) = Height.logHeight₁ (α' j) := by
    intro j
    have hbj : β j = (if 0 ≤ s then α' j else (α' j)⁻¹) := rfl
    rw [hbj]
    split_ifs with hs
    · rfl
    · exact Height.logHeight₁_inv (α' j)
  have hmon1 : ∀ j : Fin r,
      (∑ w ∈ Finset.univ.erase (NumberField.InfinitePlace.mk φ),
          ((w.mult : ℕ) : ℝ) * Real.posLog (w (β j)))
        + (∑ᶠ w : NumberField.FinitePlace K, Real.posLog (w (β j)))
      ≤ Height.logHeight₁ (α' j) := by
    intro j
    refine le_trans (est15_mon1 (NumberField.InfinitePlace.mk φ) (β j)) ?_
    rw [hβlog j]
  have hmonhyp : (∑ j : Fin r, (pDj r (dK K) σ j : ℝ) *
      ((∑ w ∈ Finset.univ.erase (NumberField.InfinitePlace.mk φ),
          ((w.mult : ℕ) : ℝ) * Real.posLog (w (β j)))
        + (∑ᶠ w : NumberField.FinitePlace K, Real.posLog (w (β j))))) ≤ acD K σ :=
    le_trans (Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hmon1 j) (Nat.cast_nonneg _))) hsl2
  have hmonbnd : (∑ w ∈ Finset.univ.erase (NumberField.InfinitePlace.mk φ), ((w.mult : ℕ) : ℝ) * Mon w)
      + (∑ᶠ w : NumberField.FinitePlace K, Monf w)
      ≤ (((|s| : ℤ) : ℝ) / 2 ^ J) * acD K σ := by
    rw [hMon, hMonf]
    exact est15_mon_bound (NumberField.InfinitePlace.mk φ) β J s hmonhyp
  have hBfinsupp : Function.HasFiniteSupport Bfin := by
    rw [hBfin]
    refine (NumberField.FinitePlace.hasFiniteMulSupport (K := K)
      (by norm_num : (2 : K) ≠ 0)).subset ?_
    intro w hw
    simp only [Function.mem_support, Function.mem_mulSupport] at hw ⊢
    intro h1
    exact hw (by rw [estCf, h1, Real.log_one]; ring)
  have hMfsupp : Function.HasFiniteSupport Monf := by
    rw [hMonf]
    have hbase : ∀ j : Fin r,
        (Function.mulSupport (fun w : NumberField.FinitePlace K => w (β j))).Finite :=
      fun j => NumberField.FinitePlace.hasFiniteMulSupport (hβne j)
    have hU : (⋃ j : Fin r, Function.mulSupport (fun w : NumberField.FinitePlace K => w (β j))).Finite := by
      have h := Set.Finite.biUnion (Set.finite_univ (α := Fin r))
        (fun j (_ : j ∈ (Set.univ : Set (Fin r))) => hbase j)
      simpa using h
    refine hU.subset ?_
    intro w hw
    simp only [Set.mem_iUnion, Function.mem_mulSupport]
    by_contra h
    simp only [not_exists, not_not] at h
    exact hw (by
      change (((|s| : ℤ) : ℝ) / 2 ^ J) * ∑ j : Fin r, (pDj r (dK K) σ j : ℝ) * Real.posLog (w (β j)) = 0
      have hone : ∀ j : Fin r, Real.posLog (w (β j)) = 0 := fun j => by
        rw [h j, Real.posLog, Real.log_one, max_self]
      simp [hone])
  have hinf : ∀ w ∈ Finset.univ.erase (NumberField.InfinitePlace.mk φ), Real.log (w X)
      ≤ Real.log (⨆ lm, w (p lm))
        + Real.log ((Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) : ℕ) : ℝ)
        + estCi K b v σ J t0 t s + Mon w := by
    intro w _
    have h := est15_place_inf (φ := φ) (α := α) (c := c) (w := w) (hXdef ▸ hX)
      (fun lm => est15_coefKJ_infl H J t0 t s w (fun lm' => est15_pi_bound H t w lm') lm)
    simp only [hXdef, hMon, hβdef] at h ⊢
    linarith [h]
  have hfin : ∀ w : NumberField.FinitePlace K, Real.log (w X)
      ≤ Real.log (⨆ lm, w (p lm)) + Bfin w + Monf w := by
    intro w
    have hcf : ∀ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ),
        Real.log (w (coefPart b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) J t0 t s lm))
          ≤ estCf K b v σ J w := by
      intro lm
      have h1 := coefPart_log_finite_le H J t0 t s lm w
      have hv : IsNonarchimedean (fun x : K => w x) := NumberField.FinitePlace.add_le w
      have hw2 : w (2 : K) ≤ 1 := by
        have h2 := hv.apply_intCast_le_one (f_zero_le := by simp) (f_one := by simp)
          (f_neg := by intro a; simp) (n := 2)
        simpa using h2
      have h2 : (0 : ℝ) ≤ - Real.log (w 2) := by
        have h3 : Real.log (w 2) ≤ 0 := Real.log_nonpos (by positivity) hw2
        linarith
      have hlt := lm.2.1.isLt
      have hle : ((lm.2.1 : ℕ) : ℝ) + 1 ≤ ((pD0 r (dK K) σ : ℕ) : ℝ) + 1 := by
        have : (lm.2.1 : ℕ) ≤ pD0 r (dK K) σ := by omega
        exact_mod_cast Nat.add_le_add_right this 1
      have h4 : (0 : ℝ) ≤ (2 : ℝ) * J * (acH K b v) := by positivity
      have h5 : ((2 : ℝ) * J * (acH K b v) * (((lm.2.1 : ℕ) : ℝ) + 1))
          ≤ ((2 : ℝ) * J * (acH K b v) * (((pD0 r (dK K) σ : ℕ) : ℝ) + 1)) := by
        nlinarith [hle, h4]
      exact le_trans h1 (by rw [estCf]; exact mul_le_mul_of_nonneg_right h5 h2)
    have h := est15_place_fin (φ := φ) (α := α) (c := c) (w := w) (hXdef ▸ hX)
      (fun lm => est15_coefKJ_fin H J t0 t s w hcf lm)
    simp only [hXdef, hBfin, hMonf, hβdef] at h ⊢
    linarith [h]
  have hbr := est15_bracket (NumberField.InfinitePlace.mk φ) X p (hXdef ▸ hX) hp0
    (estCi K b v σ J t0 t s) Bfin Mon Monf hBfinsupp hMfsupp
    (est15_height_id p hp0) hinf hfin
  have hprod := LiouvilleAux.product_formula_isolate (NumberField.InfinitePlace.mk φ) (hXdef ▸ hX)
  have hva : (NumberField.InfinitePlace.mk φ) X = ‖acg φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ := by
    rw [hXdef, NumberField.InfinitePlace.apply, phi_gKJ_eq_acg H J μ t0 t s]
  have hpos : 0 < ‖acg φ α b k L ι v σ p J μ t0 t (s : ℂ)‖ := by
    rw [← hva]
    exact NumberField.InfinitePlace.pos_iff.mpr hX
  have hlnp : Real.log (⨆ i, (NumberField.InfinitePlace.mk φ) (p i)) = lnp φ p := rfl
  have hCsum : (∑ᶠ w : NumberField.FinitePlace K, Bfin w) = estKum K b v σ J := by
    rw [hBfin, estKum]
    calc (∑ᶠ w : NumberField.FinitePlace K, estCf K b v σ J w)
        = (∑ᶠ w : NumberField.FinitePlace K,
            ((2 : ℝ) * J * (acH K b v) * (((pD0 r (dK K) σ : ℕ) : ℝ) + 1)) * (- Real.log (w 2))) := by
          simp only [estCf]
      _ = ((2 : ℝ) * J * (acH K b v) * (((pD0 r (dK K) σ : ℕ) : ℝ) + 1)) *
            (∑ᶠ w : NumberField.FinitePlace K, - Real.log (w (2 : K))) :=
          (mul_finsum (fun w : NumberField.FinitePlace K => - Real.log (w (2 : K))) _).symm
      _ = ((2 : ℝ) * J * (acH K b v) * (((pD0 r (dK K) σ : ℕ) : ℝ) + 1)) *
            ((dK K : ℝ) * Real.log 2) := by rw [est15_kummer_sum]
      _ = (2 : ℝ) * J * (acH K b v) * (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (dK K : ℝ) * Real.log 2 := by
          ring
  have hmonS : ((∑ w ∈ Finset.univ.erase (NumberField.InfinitePlace.mk φ), ((w.mult : ℕ) : ℝ) * Mon w)
      + (∑ᶠ w : NumberField.FinitePlace K, Monf w)) ≤ (((|s| : ℤ) : ℝ) / 2 ^ J) * acD K σ := hmonbnd
  have hfina := est15_final_arith (K := K) (n := n) H J t0 t s Tst m₀ (Real.log NN)
    ((∑ w ∈ Finset.univ.erase (NumberField.InfinitePlace.mk φ), ((w.mult : ℕ) : ℝ) * Mon w)
      + (∑ᶠ w : NumberField.FinitePlace K, Monf w))
    hTst htT hm1 hmd hLNN hLNN0 hmonS hlogh
  have hlog : Real.log ‖acg φ α b k L ι v σ p J μ t0 t (s : ℂ)‖
      ≥ lnp φ p - (Height.logHeight p
          + (1 - 1 / (dK K : ℝ)) * ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ)
          + 1.007 * (((|s| : ℤ) : ℝ) / 2 ^ J) * acD K σ + kumJ K b v σ J) := by
    rw [← hva]
    have hbracket : (∑ w ∈ Finset.univ.erase (NumberField.InfinitePlace.mk φ),
          ((w.mult : ℕ) : ℝ) * Real.log (w X))
        + (∑ᶠ w : NumberField.FinitePlace K, Real.log (w X))
        ≤ Height.logHeight p - m₀ * lnp φ p
          + ((dK K : ℝ) - m₀) * (Real.log NN + estCi K b v σ J t0 t s)
          + (((∑ w ∈ Finset.univ.erase (NumberField.InfinitePlace.mk φ), ((w.mult : ℕ) : ℝ) * Mon w))
              + (∑ᶠ w : NumberField.FinitePlace K, Monf w))
          + estKum K b v σ J := by
      have hb := hbr
      rw [hlnp] at hb
      rw [hCsum] at hb
      rw [hNN, hm₀]
      linarith [hb]
    have hmul : m₀ * Real.log ((NumberField.InfinitePlace.mk φ) X) ≥
        -(Height.logHeight p - m₀ * lnp φ p
          + ((dK K : ℝ) - m₀) * (Real.log NN + estCi K b v σ J t0 t s)
          + (((∑ w ∈ Finset.univ.erase (NumberField.InfinitePlace.mk φ), ((w.mult : ℕ) : ℝ) * Mon w))
              + (∑ᶠ w : NumberField.FinitePlace K, Monf w))
          + estKum K b v σ J) := by
      have hp2 : m₀ * Real.log ((NumberField.InfinitePlace.mk φ) X)
          = -((∑ w ∈ Finset.univ.erase (NumberField.InfinitePlace.mk φ),
                ((w.mult : ℕ) : ℝ) * Real.log (w X))
              + (∑ᶠ w : NumberField.FinitePlace K, Real.log (w X))) := by
        rw [hm₀]
        exact hprod
      rw [hp2]
      linarith [hbracket]
    have h2 : -(1 / m₀) * (Height.logHeight p - m₀ * lnp φ p
          + ((dK K : ℝ) - m₀) * (Real.log NN + estCi K b v σ J t0 t s)
          + (((∑ w ∈ Finset.univ.erase (NumberField.InfinitePlace.mk φ), ((w.mult : ℕ) : ℝ) * Mon w))
              + (∑ᶠ w : NumberField.FinitePlace K, Monf w))
          + estKum K b v σ J)
          = -(Height.logHeight p - m₀ * lnp φ p
          + ((dK K : ℝ) - m₀) * (Real.log NN + estCi K b v σ J t0 t s)
          + (((∑ w ∈ Finset.univ.erase (NumberField.InfinitePlace.mk φ), ((w.mult : ℕ) : ℝ) * Mon w))
              + (∑ᶠ w : NumberField.FinitePlace K, Monf w))
          + estKum K b v σ J) / m₀ := by
      field_simp
    have hL : Real.log ((NumberField.InfinitePlace.mk φ) X) ≥
        -(1 / m₀) * (Height.logHeight p - m₀ * lnp φ p
          + ((dK K : ℝ) - m₀) * (Real.log NN + estCi K b v σ J t0 t s)
          + (((∑ w ∈ Finset.univ.erase (NumberField.InfinitePlace.mk φ), ((w.mult : ℕ) : ℝ) * Mon w))
              + (∑ᶠ w : NumberField.FinitePlace K, Monf w))
          + estKum K b v σ J) := by
      rw [h2]
      exact (div_le_iff₀' hmpos).mpr (by linarith [hmul])
    have hexp : -(1 / m₀) * (Height.logHeight p - m₀ * lnp φ p
          + ((dK K : ℝ) - m₀) * (Real.log NN + estCi K b v σ J t0 t s)
          + (((∑ w ∈ Finset.univ.erase (NumberField.InfinitePlace.mk φ), ((w.mult : ℕ) : ℝ) * Mon w))
              + (∑ᶠ w : NumberField.FinitePlace K, Monf w))
          + estKum K b v σ J)
        = lnp φ p - ((1 / m₀) * Height.logHeight p
          + (1 / m₀) * ((dK K : ℝ) - m₀) * (Real.log NN + estCi K b v σ J t0 t s)
          + (1 / m₀) * (((∑ w ∈ Finset.univ.erase (NumberField.InfinitePlace.mk φ), ((w.mult : ℕ) : ℝ) * Mon w))
              + (∑ᶠ w : NumberField.FinitePlace K, Monf w))
          + (1 / m₀) * estKum K b v σ J) := by
      field_simp
      ring
    rw [hexp] at hL
    linarith [hL, hfina]
  exact (Real.le_log_iff_exp_le hpos).mp hlog

end Work.BW
