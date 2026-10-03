import Mathlib
import Submission.Work.Peluse.U2Inv.Defs

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `ℓ¹` norm of the Fourier transform of Peluse's weight `ν`

This module proves

`∑_k ‖𝓕 ν_m (k)‖ = Gmod L / m`

for Peluse's weight `ν_m` on the auxiliary cyclic group `ZMod (Gmod L)` (`Gmod L = 4L+1`),
where `ν_m` is the distribution of `u - u'` for two independent uniform points `u, u'` of
`{1, …, m}` (`m ≤ Gmod L`), and `𝓕 = ZMod.dft` is the discrete Fourier transform with respect to
the standard additive character.

The argument is the classical one for such an "averaging operator" weight:

* `𝓕 ν_m (k) = m^{-2} · conj(s k) · s k` where `s k = ∑_{u ∈ [1,m]} χ(u k)` is the incomplete
  character sum — the Fourier transform factorises because `ν_m` is the distribution of a
  difference.  Hence `‖𝓕 ν_m (k)‖ = m^{-2} ‖s k‖²`;
* `∑_k ‖s k‖² = ∑_{u,u' ∈ [1,m]} ∑_k χ((u-u')k) = m · #(ZMod (Gmod L)) = m · Gmod L`, by the
  orthogonality of characters (`∑_k χ(a k) = 0` for `a ≠ 0`) and the fact that `u ↦ (u : ZMod N)`
  is injective on `{1, …, m}` when `m ≤ N`.

Putting the two together gives `∑_k ‖𝓕 ν_m (k)‖ = m^{-2} · m · Gmod L = Gmod L / m`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.U2Inv

noncomputable section

/-! ## Elementary facts about the standard additive character -/

/-- The standard additive character on `ZMod N` takes conjugate values at opposite points:
`conj (χ x) = χ (-x)`. -/
private lemma aux_star_stdAddChar {N : ℕ} [NeZero N] (x : ZMod N) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv (ZMod.toCircle) x,
    Circle.coe_inv_eq_conj]
  exact rfl

/-- Orthogonality of the standard additive character:
`∑_k χ (a k) = #(ZMod N)` if `a = 0` and `0` otherwise. -/
private lemma aux_sum_stdAddChar_mul {N : ℕ} [NeZero N] (a : ZMod N) :
    ∑ k : ZMod N, ZMod.stdAddChar (a * k) = if a = 0 then (N : ℂ) else 0 := by
  have h := AddChar.sum_mulShift (ψ := ZMod.stdAddChar (N := N)) a
    (ZMod.isPrimitive_stdAddChar N)
  simp only [ZMod.card, Nat.cast_ite, Nat.cast_zero] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]

/-- Regrouping a sum weighted by the size of the fibres of a map into a sum over the source. -/
private lemma aux_sum_card_filter_mul {α β : Type*} [Fintype β] [DecidableEq β]
    (S : Finset α) (g : α → β) (F : β → ℂ) :
    ∑ j : β, F j * ((S.filter (fun i => g i = j)).card : ℂ) = ∑ i ∈ S, F (g i) := by
  rw [← Finset.sum_fiberwise' S g F]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- The incomplete character sum `s k = ∑_{u ∈ {1,…,m}} χ (u k)`. -/
private def auxNuChar (L m : ℕ) (k : ZMod (Gmod L)) : ℂ :=
  ∑ u ∈ Finset.Icc 1 m, ZMod.stdAddChar ((u : ZMod (Gmod L)) * k)

/-- The map `ℕ → ZMod N`, `u ↦ u`, is injective on `{1, …, m}` as soon as `m ≤ N`. -/
private lemma aux_natCast_inj_of_mem_Icc {N m u v : ℕ} (hu : u ∈ Finset.Icc 1 m)
    (hv : v ∈ Finset.Icc 1 m) (hmN : m ≤ N) (h : (u : ZMod N) = (v : ZMod N)) : u = v := by
  have hu1 : 1 ≤ u := (Finset.mem_Icc.mp hu).1
  have hum : u ≤ m := (Finset.mem_Icc.mp hu).2
  have hv1 : 1 ≤ v := (Finset.mem_Icc.mp hv).1
  have hvm : v ≤ m := (Finset.mem_Icc.mp hv).2
  rcases le_total u v with huv | hvu
  · have hdvd : N ∣ v - u := by
      have h0 : ((v - u : ℕ) : ZMod N) = 0 := by
        rw [Nat.cast_sub huv, h, sub_self]
      exact (ZMod.natCast_eq_zero_iff (v - u) N).mp h0
    have hlt : v - u < N := by omega
    have h0 : v - u = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega
  · have hdvd : N ∣ u - v := by
      have h0 : ((u - v : ℕ) : ZMod N) = 0 := by
        rw [Nat.cast_sub hvu, ← h, sub_self]
      exact (ZMod.natCast_eq_zero_iff (u - v) N).mp h0
    have hlt : u - v < N := by omega
    have h0 : u - v = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega

/-! ## The Fourier transform of `ν` -/

private lemma aux_dft_nu_apply (L m : ℕ) (k : ZMod (Gmod L)) :
    ZMod.dft (nu L m) k = (((m : ℂ) ^ 2)⁻¹) *
      ∑ p ∈ (Finset.Icc 1 m).product (Finset.Icc 1 m),
        ZMod.stdAddChar (-(((p.1 : ZMod (Gmod L)) - (p.2 : ZMod (Gmod L))) * k)) := by
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul]
  calc ∑ x : ZMod (Gmod L), ZMod.stdAddChar (-(x * k)) * (nu L m x)
      = ∑ x : ZMod (Gmod L), ZMod.stdAddChar (-(x * k)) *
          (((m : ℂ) ^ 2)⁻¹ * ↑{p ∈ (Finset.Icc 1 m).product (Finset.Icc 1 m) |
              ((p.1 : ℕ) : ZMod (Gmod L)) - ((p.2 : ℕ) : ZMod (Gmod L)) = x}.card) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [nu]
    _ = ∑ x : ZMod (Gmod L), (((m : ℂ) ^ 2)⁻¹) *
          (ZMod.stdAddChar (-(x * k)) * ↑{p ∈ (Finset.Icc 1 m).product (Finset.Icc 1 m) |
              ((p.1 : ℕ) : ZMod (Gmod L)) - ((p.2 : ℕ) : ZMod (Gmod L)) = x}.card) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ = (((m : ℂ) ^ 2)⁻¹) * ∑ x : ZMod (Gmod L), ZMod.stdAddChar (-(x * k)) *
          ↑{p ∈ (Finset.Icc 1 m).product (Finset.Icc 1 m) |
              ((p.1 : ℕ) : ZMod (Gmod L)) - ((p.2 : ℕ) : ZMod (Gmod L)) = x}.card := by
        rw [Finset.mul_sum]
    _ = (((m : ℂ) ^ 2)⁻¹) * ∑ p ∈ (Finset.Icc 1 m).product (Finset.Icc 1 m),
          ZMod.stdAddChar (-(((((p.1 : ℕ) : ZMod (Gmod L)) -
            ((p.2 : ℕ) : ZMod (Gmod L))) * k))) := by
        rw [aux_sum_card_filter_mul]

/-- The double sum appearing in the Fourier transform of `ν` factorises into the product of the
incomplete character sum and its conjugate. -/
private lemma aux_sum_product_eq (L m : ℕ) (k : ZMod (Gmod L)) :
    ∑ p ∈ (Finset.Icc 1 m).product (Finset.Icc 1 m),
        ZMod.stdAddChar (-(((p.1 : ZMod (Gmod L)) - (p.2 : ZMod (Gmod L))) * k))
      = star (auxNuChar L m k) * auxNuChar L m k := by
  have hxy : ∀ x y : ℕ,
      ZMod.stdAddChar (-(((x : ZMod (Gmod L)) - (y : ZMod (Gmod L))) * k))
        = ZMod.stdAddChar (-((x : ZMod (Gmod L)) * k)) *
          ZMod.stdAddChar ((y : ZMod (Gmod L)) * k) := by
    intro x y
    rw [sub_mul, neg_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, mul_comm]
  simp only [hxy]
  calc ∑ p ∈ (Finset.Icc 1 m).product (Finset.Icc 1 m),
        ZMod.stdAddChar (-((p.1 : ZMod (Gmod L)) * k)) *
          ZMod.stdAddChar ((p.2 : ZMod (Gmod L)) * k)
      = ∑ x ∈ Finset.Icc 1 m, ∑ y ∈ Finset.Icc 1 m,
          ZMod.stdAddChar (-((x : ZMod (Gmod L)) * k)) *
            ZMod.stdAddChar ((y : ZMod (Gmod L)) * k) :=
        Finset.sum_product (Finset.Icc 1 m) (Finset.Icc 1 m) _
    _ = (∑ x ∈ Finset.Icc 1 m, ZMod.stdAddChar (-((x : ZMod (Gmod L)) * k)))
          * (∑ y ∈ Finset.Icc 1 m, ZMod.stdAddChar ((y : ZMod (Gmod L)) * k)) :=
        (Finset.sum_mul_sum _ _ _ _).symm
    _ = star (auxNuChar L m k) * auxNuChar L m k := by
        congr 1
        rw [auxNuChar, star_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        exact (aux_star_stdAddChar _).symm

/-- The Fourier transform of the weight `ν_m` is `m^{-2}` times the squared modulus of the
incomplete character sum. -/
private lemma aux_dft_nu_eq (L m : ℕ) (k : ZMod (Gmod L)) :
    ZMod.dft (nu L m) k = (((m : ℂ) ^ 2)⁻¹) * star (auxNuChar L m k) * auxNuChar L m k := by
  rw [aux_dft_nu_apply, aux_sum_product_eq]
  ring

/-- The norm of the Fourier transform of `ν_m` is `m^{-2} ‖s k‖² = m^{-2} normSq (s k)`. -/
private lemma aux_norm_dft_nu (L m : ℕ) (k : ZMod (Gmod L)) :
    ‖ZMod.dft (nu L m) k‖ = ((m : ℝ) ^ 2)⁻¹ * Complex.normSq (auxNuChar L m k) := by
  have h : ZMod.dft (nu L m) k
      = (((m : ℂ) ^ 2)⁻¹) * (star (auxNuChar L m k) * auxNuChar L m k) := by
    rw [aux_dft_nu_eq]
    ring
  rw [h, show star (auxNuChar L m k) * auxNuChar L m k
        = ((Complex.normSq (auxNuChar L m k) : ℝ) : ℂ) from
      (Complex.normSq_eq_conj_mul_self (z := auxNuChar L m k)).symm,
    norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  rw [show ‖((Complex.normSq (auxNuChar L m k) : ℝ) : ℂ)‖ = Complex.normSq (auxNuChar L m k)
      from by rw [Complex.normSq_eq_norm_sq]; simp]

/-! ## The `ℓ²` norm of the incomplete character sum -/

private lemma aux_star_mul_nuChar (L m : ℕ) (k : ZMod (Gmod L)) :
    (starRingEnd ℂ) (auxNuChar L m k) * auxNuChar L m k
      = ∑ u ∈ Finset.Icc 1 m, ∑ v ∈ Finset.Icc 1 m,
          ZMod.stdAddChar ((((v : ℕ) : ZMod (Gmod L)) -
            ((u : ℕ) : ZMod (Gmod L))) * k) := by
  rw [auxNuChar, map_sum (starRingEnd ℂ), Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rw [show (starRingEnd ℂ) (ZMod.stdAddChar ((u : ZMod (Gmod L)) * k))
        = ZMod.stdAddChar (-((u : ZMod (Gmod L)) * k)) from aux_star_stdAddChar _,
    ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- Summing the orthogonality relation over the pairs `(u, v) ∈ {1,…,m}²`: only the diagonal
survives, because `u ↦ (u : ZMod N)` is injective on `{1, …, m}` when `m ≤ N`. -/
private lemma aux_sum_ite_eq (N m : ℕ) (hmN : m ≤ N) :
    (∑ u ∈ Finset.Icc 1 m, ∑ v ∈ Finset.Icc 1 m,
        (if ((v : ZMod N) - (u : ZMod N)) = 0 then (N : ℂ) else 0)) = ((m * N : ℕ) : ℂ) := by
  have hiff : ∀ u v : ℕ, u ∈ Finset.Icc 1 m → v ∈ Finset.Icc 1 m →
      (((v : ZMod N) - (u : ZMod N) = 0) ↔ u = v) := by
    intro u v hu hv
    constructor
    · intro h
      have h2 : (u : ZMod N) = (v : ZMod N) := by
        have h3 : (v : ZMod N) = (u : ZMod N) := sub_eq_zero.mp h
        rw [h3]
      exact aux_natCast_inj_of_mem_Icc hu hv hmN h2
    · intro h
      rw [h, sub_self]
  have hL : (∑ u ∈ Finset.Icc 1 m, ∑ v ∈ Finset.Icc 1 m,
        (if ((v : ZMod N) - (u : ZMod N)) = 0 then (N : ℂ) else 0))
      = ∑ u ∈ Finset.Icc 1 m, (N : ℂ) := by
    refine Finset.sum_congr rfl fun u hu => ?_
    have hinner : (∑ v ∈ Finset.Icc 1 m,
          (if ((v : ZMod N) - (u : ZMod N)) = 0 then (N : ℂ) else 0))
        = ∑ v ∈ Finset.Icc 1 m, (if u = v then (N : ℂ) else 0) :=
      Finset.sum_congr rfl fun v hv => by simp only [hiff u v hu hv]
    rw [hinner, Finset.sum_ite_eq (Finset.Icc 1 m) u (fun _ => (N : ℂ)), if_pos hu]
  rw [hL, Finset.sum_const, nsmul_eq_mul]
  simp

/-- The `ℓ²` norm of the incomplete character sum: `∑_k ‖s k‖² = m · Gmod L`. -/
private lemma aux_sum_normSq (L m : ℕ) (hmL : m ≤ Gmod L) :
    ∑ k : ZMod (Gmod L), Complex.normSq (auxNuChar L m k) = (m : ℝ) * (Gmod L) := by
  have hcomplex :
      ((∑ k : ZMod (Gmod L), Complex.normSq (auxNuChar L m k) : ℝ) : ℂ)
        = ((((m : ℝ) * (Gmod L : ℝ)) : ℝ) : ℂ) := by
    have h1 : ((∑ k : ZMod (Gmod L), Complex.normSq (auxNuChar L m k) : ℝ) : ℂ)
        = ∑ k : ZMod (Gmod L), ((Complex.normSq (auxNuChar L m k) : ℝ) : ℂ) := by
      simp
    rw [h1]
    simp only [Complex.normSq_eq_conj_mul_self]
    rw [Finset.sum_congr rfl (fun k _ => aux_star_mul_nuChar L m k)]
    calc ∑ k : ZMod (Gmod L), ∑ u ∈ Finset.Icc 1 m, ∑ v ∈ Finset.Icc 1 m,
          ZMod.stdAddChar ((((v : ℕ) : ZMod (Gmod L)) -
            ((u : ℕ) : ZMod (Gmod L))) * k)
        = ∑ u ∈ Finset.Icc 1 m, ∑ k : ZMod (Gmod L), ∑ v ∈ Finset.Icc 1 m,
            ZMod.stdAddChar ((((v : ℕ) : ZMod (Gmod L)) -
              ((u : ℕ) : ZMod (Gmod L))) * k) := Finset.sum_comm
      _ = ∑ u ∈ Finset.Icc 1 m, ∑ v ∈ Finset.Icc 1 m, ∑ k : ZMod (Gmod L),
            ZMod.stdAddChar ((((v : ℕ) : ZMod (Gmod L)) -
              ((u : ℕ) : ZMod (Gmod L))) * k) := by
          refine Finset.sum_congr rfl fun u _ => ?_
          exact Finset.sum_comm
      _ = ∑ u ∈ Finset.Icc 1 m, ∑ v ∈ Finset.Icc 1 m,
            (if ((((v : ℕ) : ZMod (Gmod L)) - ((u : ℕ) : ZMod (Gmod L))) = 0) then (Gmod L : ℂ) else 0) := by
          refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
          exact aux_sum_stdAddChar_mul _
      _ = ((m * Gmod L : ℕ) : ℂ) := aux_sum_ite_eq (Gmod L) m hmL
      _ = ((((m : ℝ) * (Gmod L : ℝ)) : ℝ) : ℂ) := by push_cast; ring
  exact Complex.ofReal_inj.mp hcomplex

/-! ## The main statement -/

theorem u2inv_sum_dft_nu (L m : ℕ) (hm : 1 ≤ m) (hmL : m ≤ Work.Peluse.U2Inv.Gmod L) :
    ∑ k : ZMod (Work.Peluse.U2Inv.Gmod L), ‖ZMod.dft (Work.Peluse.U2Inv.nu L m) k‖
      = (Work.Peluse.U2Inv.Gmod L : ℝ) / (m : ℝ) := by
  have h1 : ∑ k : ZMod (Gmod L), ‖ZMod.dft (nu L m) k‖
      = (((m : ℝ) ^ 2)⁻¹) * ∑ k : ZMod (Gmod L), Complex.normSq (auxNuChar L m k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => aux_norm_dft_nu L m k
  rw [h1, aux_sum_normSq L m hmL]
  have hm0 : (m : ℝ) ≠ 0 := by
    have h : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    positivity
  have h1 : ((m : ℝ) ^ 2)⁻¹ = ((m : ℝ)⁻¹) ^ 2 := by rw [inv_pow]
  have h2 : (m : ℝ)⁻¹ * (m : ℝ) = 1 := inv_mul_cancel₀ hm0
  rw [h1, div_eq_mul_inv, sq]
  calc (m : ℝ)⁻¹ * (m : ℝ)⁻¹ * ((m : ℝ) * (Gmod L : ℝ))
      = ((m : ℝ)⁻¹ * (m : ℝ)) * ((m : ℝ)⁻¹ * (Gmod L : ℝ)) := by ring
    _ = (m : ℝ)⁻¹ * (Gmod L : ℝ) := by rw [h2, one_mul]
    _ = (Gmod L : ℝ) * (m : ℝ)⁻¹ := by ring

end

end Work.Peluse.U2Inv
