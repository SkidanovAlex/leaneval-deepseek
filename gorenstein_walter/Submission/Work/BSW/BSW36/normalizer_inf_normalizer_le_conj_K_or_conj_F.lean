/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, §3 leaf 3.6)

# BSW §3.6: `N_N(R)` for `r ≠ p` lies in a conjugate of `K` or of `F = C_G(x)`

Bender, *The Brauer–Suzuki–Wall theorem*, Illinois J. Math. **18** (1974) 229–235, (3.6):
"Let `X ≠ 1` be a p-subgroup of `G`, and `R` a Sylow `r`-subgroup of `N = N_G(X)` for a prime
`r ≠ p`.  Since both `F` and `K` are t.i. subgroups of `G`, and have index 2 in their normalizer,
`N(R)` is conjugate to a subgroup of `F` or `K` (in particular `N(R)` is abelian)."

We prove the (slightly more general) statement with `R` any nontrivial `r`-subgroup of `N_G(X)`
(`r ≠ p` a prime): the group `N_G(X) ⊓ N_G(R)` is contained in a conjugate of `K`, or in a
conjugate of `F = C_G(x)`.

The proof: `N_G(X)` has odd order (`Work.BSW.S3.normalizer_odd_order`), so every subgroup of it
has odd order.  Choose `1 ≠ w` in the centre of `R`.  By the dichotomy of (3.5)
(`Work.BSW.S3.mem_HG_or_conj_centralizer`, as `orderOf w` is an `r`-power and `r ≠ p`) either
`w` is conjugate into `K`, or `w` is conjugate into `F`.

* In the first case `C_G(w) ≤ H^g = C_G(t)^g` (the "`K^#` remark" of p. 232, here
  `mem_centralizer_t_of_commute_mem_K`), so the odd-order group `R ≤ C_G(w)` lands in
  `K^g = conjSub g K`; and since `K` is a t.i. subgroup, `v ∈ N_G(R)` forces
  `v K^g v⁻¹ = K^g`, i.e. `v ∈ N_G(K^g) = H^g`, whose odd-order elements lie in `K^g`.
* In the second case `C_G(w) = F^g` (`Work.BSW.S3.centralizer_eq_of_mem_conjSub_centralizer_x`),
  so `R ≤ F^g`; since `F` is t.i. with normalizer of index 2, `v ∈ N_G(R)` forces
  `v ∈ N_G(F^g)`, whose odd-order elements lie in `F^g`.
-/
import Mathlib
import Submission.Work.BSW.S3.s36aux

namespace Work.BSW.BSW36

open Subgroup Work.GW2
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G} {x : G} {p : ℕ}

/-! ## The "`K^#` remark" (Bender 1974, p. 232) -/

/-- An element commuting with a non-identity element of the TI-subgroup `K` lies in `C_G(t)`. -/
theorem mem_centralizer_t_of_commute_mem_K (h : BSWHyps2 G t s K) {y u : G} (hyK : y ∈ K)
    (hy1 : y ≠ 1) (hu : u * y = y * u) : u ∈ Subgroup.centralizer ({t} : Set G) := by
  by_contra huC
  have huC' : u⁻¹ ∉ Subgroup.centralizer ({t} : Set G) := fun hh =>
    huC (by simpa using (Subgroup.centralizer ({t} : Set G)).inv_mem hh)
  have hbot := Work.BSW.TI h u⁻¹ huC'
  have hyconj : y ∈ conjSub u⁻¹ K := by
    rw [conjSub, Subgroup.mem_map]
    refine ⟨y, hyK, ?_⟩
    show MulAut.conj u⁻¹ y = y
    rw [MulAut.conj_apply, inv_inv]
    calc u⁻¹ * y * u = u⁻¹ * (y * u) := by group
      _ = u⁻¹ * (u * y) := by rw [hu.symm]
      _ = y := by group
  have hmem : y ∈ K ⊓ conjSub u⁻¹ K := ⟨hyK, hyconj⟩
  rw [hbot] at hmem
  exact hy1 (Subgroup.mem_bot.mp hmem)

/-! ## Transporting the "odd order" lemmas along conjugation -/

/-- Conjugated form of `Work.BSW.S3.mem_K_of_mem_centralizer_t_of_odd`. -/
theorem mem_conjSub_K_of_mem_conjSub_centralizer_t_of_odd (h : BSWHyps2 G t s K) {g v : G}
    (hv : v ∈ conjSub g (Subgroup.centralizer ({t} : Set G))) (hodd : Odd (orderOf v)) :
    v ∈ conjSub g K := by
  rw [Work.BSW.S3.mem_conjSub_iff] at hv ⊢
  have h1 : orderOf (g⁻¹ * v * g) = orderOf v := by
    have h2 := Work.BSW.S3.orderOf_conj_eq g (g⁻¹ * v * g)
    rw [show g * (g⁻¹ * v * g) * g⁻¹ = v from by group] at h2
    exact h2.symm
  exact Work.BSW.S3.mem_K_of_mem_centralizer_t_of_odd h hv (by rw [h1]; exact hodd)

/-- Conjugated form of `Work.BSW.S3.mem_centralizer_x_of_mem_normalizer_of_odd`. -/
theorem mem_conjSub_centralizer_x_of_mem_conjSub_normalizer_of_odd (h : BSWCase2 G t s K x p)
    {g v : G}
    (hv : v ∈ conjSub g (Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G)) : Set G)))
    (hodd : Odd (orderOf v)) : v ∈ conjSub g (Subgroup.centralizer ({x} : Set G)) := by
  rw [Work.BSW.S3.mem_conjSub_iff] at hv ⊢
  have h1 : orderOf (g⁻¹ * v * g) = orderOf v := by
    have h2 := Work.BSW.S3.orderOf_conj_eq g (g⁻¹ * v * g)
    rw [show g * (g⁻¹ * v * g) * g⁻¹ = v from by group] at h2
    exact h2.symm
  exact Work.BSW.S3.mem_centralizer_x_of_mem_normalizer_of_odd h hv (by rw [h1]; exact hodd)

/-! ## `K` and `F` are TI on their conjugates -/

/-- Two conjugates of `K` that share a non-identity element coincide (`K` is a t.i. subgroup
with `N_G(K) = C_G(t)`). -/
theorem conjSub_K_inf_eq_of_ne_bot (h : BSWHyps2 G t s K) {g1 g2 : G}
    (hne : conjSub g1 K ⊓ conjSub g2 K ≠ ⊥) : conjSub g1 K = conjSub g2 K := by
  haveI : Nontrivial ↥(conjSub g1 K ⊓ conjSub g2 K) := by
    rw [Subgroup.nontrivial_iff_ne_bot]; exact hne
  obtain ⟨z, hz1⟩ := exists_ne (1 : ↥(conjSub g1 K ⊓ conjSub g2 K))
  set a : G := (z : G) with hadef
  have ha : a ∈ conjSub g1 K ⊓ conjSub g2 K := z.2
  have ha1 : a ≠ 1 := fun hc => hz1 (Subtype.ext hc)
  have hbK : g1⁻¹ * a * g1 ∈ K := (Work.BSW.S3.mem_conjSub_iff).mp ha.1
  have hb2 : g1⁻¹ * a * g1 ∈ conjSub (g1⁻¹ * g2) K := by
    rw [Work.BSW.S3.mem_conjSub_iff]
    have hh := (Work.BSW.S3.mem_conjSub_iff).mp ha.2
    have e : (g1⁻¹ * g2)⁻¹ * (g1⁻¹ * a * g1) * (g1⁻¹ * g2) = g2⁻¹ * a * g2 := by group
    rwa [e]
  have hb1 : g1⁻¹ * a * g1 ≠ 1 := by
    intro hc
    apply ha1
    calc a = g1 * (g1⁻¹ * a * g1) * g1⁻¹ := by group
      _ = 1 := by rw [hc]; group
  have hinf : K ⊓ conjSub (g1⁻¹ * g2) K ≠ ⊥ := by
    intro hbot
    have : g1⁻¹ * a * g1 ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact ⟨hbK, hb2⟩
    exact hb1 (Subgroup.mem_bot.mp this)
  have hconjK : conjSub (g1⁻¹ * g2) K = K := by
    have hmC : g1⁻¹ * g2 ∈ Subgroup.centralizer ({t} : Set G) := by
      by_contra hc
      exact hinf (Work.BSW.TI h (g1⁻¹ * g2) hc)
    have hmN : g1⁻¹ * g2 ∈ Subgroup.normalizer (K : Set G) := by
      rwa [Work.BSW.Api.normalizer_K_eq h]
    have := (Subgroup.mem_normalizer_iff_map_conj_eq).mp hmN
    rwa [conjSub]
  calc conjSub g1 K = conjSub g1 (conjSub (g1⁻¹ * g2) K) := by rw [hconjK]
    _ = conjSub (g1 * (g1⁻¹ * g2)) K := Work.BSW.S3.conjSub_conjSub
    _ = conjSub g2 K := by rw [show g1 * (g1⁻¹ * g2) = g2 from by group]

/-- Two conjugates of `F = C_G(x)` that share a non-identity element coincide (`F` is a t.i.
subgroup, `Work.BSW.S3.centralizer_x_inf_conjSub_eq_bot`). -/
theorem conjSub_F_inf_eq_of_ne_bot (h : BSWCase2 G t s K x p) {g1 g2 : G}
    (hne : conjSub g1 (Subgroup.centralizer ({x} : Set G)) ⊓
      conjSub g2 (Subgroup.centralizer ({x} : Set G)) ≠ ⊥) :
    conjSub g1 (Subgroup.centralizer ({x} : Set G)) =
      conjSub g2 (Subgroup.centralizer ({x} : Set G)) := by
  haveI : Nontrivial ↥(conjSub g1 (Subgroup.centralizer ({x} : Set G)) ⊓
      conjSub g2 (Subgroup.centralizer ({x} : Set G))) := by
    rw [Subgroup.nontrivial_iff_ne_bot]; exact hne
  obtain ⟨z, hz1⟩ := exists_ne (1 : ↥(conjSub g1 (Subgroup.centralizer ({x} : Set G)) ⊓
      conjSub g2 (Subgroup.centralizer ({x} : Set G))))
  set a : G := (z : G) with hadef
  have ha : a ∈ conjSub g1 (Subgroup.centralizer ({x} : Set G)) ⊓
      conjSub g2 (Subgroup.centralizer ({x} : Set G)) := z.2
  have ha1 : a ≠ 1 := fun hc => hz1 (Subtype.ext hc)
  have hbK : g1⁻¹ * a * g1 ∈ Subgroup.centralizer ({x} : Set G) :=
    (Work.BSW.S3.mem_conjSub_iff).mp ha.1
  have hb2 : g1⁻¹ * a * g1 ∈ conjSub (g1⁻¹ * g2) (Subgroup.centralizer ({x} : Set G)) := by
    rw [Work.BSW.S3.mem_conjSub_iff]
    have hh := (Work.BSW.S3.mem_conjSub_iff).mp ha.2
    have e : (g1⁻¹ * g2)⁻¹ * (g1⁻¹ * a * g1) * (g1⁻¹ * g2) = g2⁻¹ * a * g2 := by group
    rwa [e]
  have hb1 : g1⁻¹ * a * g1 ≠ 1 := by
    intro hc
    apply ha1
    calc a = g1 * (g1⁻¹ * a * g1) * g1⁻¹ := by group
      _ = 1 := by rw [hc]; group
  have hinf : Subgroup.centralizer ({x} : Set G) ⊓
      conjSub (g1⁻¹ * g2) (Subgroup.centralizer ({x} : Set G)) ≠ ⊥ := by
    intro hbot
    have : g1⁻¹ * a * g1 ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact ⟨hbK, hb2⟩
    exact hb1 (Subgroup.mem_bot.mp this)
  have hconjF : conjSub (g1⁻¹ * g2) (Subgroup.centralizer ({x} : Set G)) =
      Subgroup.centralizer ({x} : Set G) := by
    have hmN : g1⁻¹ * g2 ∈
        Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G)) : Set G) := by
      by_contra hc
      exact hinf (Work.BSW.S3.centralizer_x_inf_conjSub_eq_bot h hc)
    have := (Subgroup.mem_normalizer_iff_map_conj_eq).mp hmN
    rwa [conjSub]
  calc conjSub g1 (Subgroup.centralizer ({x} : Set G))
      = conjSub g1 (conjSub (g1⁻¹ * g2) (Subgroup.centralizer ({x} : Set G))) := by rw [hconjF]
    _ = conjSub (g1 * (g1⁻¹ * g2)) (Subgroup.centralizer ({x} : Set G)) :=
        Work.BSW.S3.conjSub_conjSub
    _ = conjSub g2 (Subgroup.centralizer ({x} : Set G)) :=
        by rw [show g1 * (g1⁻¹ * g2) = g2 from by group]

/-! ## The leaf -/

theorem normalizer_inf_normalizer_le_conj_K_or_conj_F {G : Type} [Group G] [Finite G]
    {t s : G} {K : Subgroup G} {x : G} {p : ℕ} (h : Work.BSW.BSWCase2 G t s K x p)
    {X : Subgroup G} (hX : X ≠ ⊥) (hXp : IsPGroup p X) {r : ℕ} (hr : r.Prime) (hrp : r ≠ p)
    {R : Subgroup G} (hRle : R ≤ Subgroup.normalizer (X : Set G)) (hRne : R ≠ ⊥)
    (hRr : IsPGroup r R) :
    (∃ g, Subgroup.normalizer (X : Set G) ⊓ Subgroup.normalizer (R : Set G) ≤ Work.GW2.conjSub g K) ∨
    (∃ g, Subgroup.normalizer (X : Set G) ⊓ Subgroup.normalizer (R : Set G) ≤
      Work.GW2.conjSub g (Subgroup.centralizer ({x} : Set G))) := by
  haveI : Fact r.Prime := ⟨hr⟩
  -- `N_G(X)` has odd order
  have hNodd : Odd (Nat.card ↥(Subgroup.normalizer (X : Set G))) :=
    Work.BSW.S3.normalizer_odd_order h hX hXp
  -- a non-identity element `w` of the centre of `R`
  haveI : Nontrivial ↥R := by rw [Subgroup.nontrivial_iff_ne_bot]; exact hRne
  haveI : Nontrivial ↥(Subgroup.center ↥R) := IsPGroup.center_nontrivial hRr
  obtain ⟨z, hz1⟩ := exists_ne (1 : ↥(Subgroup.center ↥R))
  set w : G := ((z : ↥R) : G) with hwdef
  have hwR : w ∈ R := (z : ↥R).2
  have hw1 : w ≠ 1 := fun hc => hz1 (Subtype.ext (Subtype.ext hc))
  have hwcenter : ∀ u ∈ R, u * w = w * u := by
    intro u hu
    have hmem := Subgroup.mem_center_iff.mp z.2 (⟨u, hu⟩ : ↥R)
    have hval := congrArg (fun y : ↥R => (y : G)) hmem
    simp only [Subgroup.coe_mul] at hval
    simpa [hwdef] using hval
  -- `orderOf w` is a power of `r`, hence `≠ p`
  have hword_ne_p : orderOf w ≠ p := by
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf).mp hRr ⟨w, hwR⟩
    have hcoe : orderOf w = r ^ j := (Subgroup.orderOf_coe (⟨w, hwR⟩ : ↥R)).trans hj
    intro hp
    rw [hcoe] at hp
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hp
      exact (Work.BSW.S3.prime (h := h)).ne_one hp.symm
    have hdvd : r ∣ p := by rw [← hp]; exact dvd_pow_self r hj0
    exact hrp ((Nat.Prime.dvd_iff_eq (Work.BSW.S3.prime (h := h)) hr.ne_one).mp hdvd).symm
  -- dichotomy of (3.5)
  rcases Work.BSW.S3.mem_HG_or_conj_centralizer (h := h) hw1 hword_ne_p with hwH | ⟨g0, hg0⟩
  · -- `w` is conjugate into `K`
    obtain ⟨h0, hh0⟩ := hwH
    have hh1 : h0 * w * h0⁻¹ ≠ 1 := by
      intro hc
      apply hw1
      calc w = h0⁻¹ * (h0 * w * h0⁻¹) * h0 := by group
        _ = 1 := by rw [hc]; group
    have hhodd : Odd (orderOf (h0 * w * h0⁻¹)) := by
      rw [Work.BSW.S3.orderOf_conj_eq h0 w]
      exact Odd.of_dvd_nat hNodd (Subgroup.orderOf_dvd_natCard _ (hRle hwR))
    have hhK : h0 * w * h0⁻¹ ∈ K :=
      Work.BSW.S3.mem_K_of_mem_centralizer_t_of_odd (Work.BSW.S3.hyps (h := h)) hh0 hhodd
    refine Or.inl ⟨h0⁻¹, ?_⟩
    -- `R ≤ conjSub h0⁻¹ K`
    have hRK : R ≤ conjSub h0⁻¹ K := by
      intro u hu
      have hcomm : (h0 * u * h0⁻¹) * (h0 * w * h0⁻¹) =
          (h0 * w * h0⁻¹) * (h0 * u * h0⁻¹) := by
        rw [show (h0 * u * h0⁻¹) * (h0 * w * h0⁻¹) = h0 * (u * w) * h0⁻¹ by group,
          show (h0 * w * h0⁻¹) * (h0 * u * h0⁻¹) = h0 * (w * u) * h0⁻¹ by group,
          hwcenter u hu]
      have hmem : h0 * u * h0⁻¹ ∈ Subgroup.centralizer ({t} : Set G) :=
        mem_centralizer_t_of_commute_mem_K (Work.BSW.S3.hyps (h := h)) hhK hh1 hcomm
      have huC : u ∈ conjSub h0⁻¹ (Subgroup.centralizer ({t} : Set G)) := by
        rw [Work.BSW.S3.mem_conjSub_iff]
        simpa using hmem
      exact mem_conjSub_K_of_mem_conjSub_centralizer_t_of_odd (Work.BSW.S3.hyps (h := h)) huC
        (Odd.of_dvd_nat hNodd (Subgroup.orderOf_dvd_natCard _ (hRle hu)))
    intro v hv
    rw [Subgroup.mem_inf] at hv
    obtain ⟨hvX, hvR⟩ := hv
    have hvodd : Odd (orderOf v) :=
      Odd.of_dvd_nat hNodd (Subgroup.orderOf_dvd_natCard _ hvX)
    have hvconjR : conjSub v R = R := Subgroup.mem_normalizer_iff_map_conj_eq.mp hvR
    have hle2 : R ≤ conjSub (v * h0⁻¹) K := by
      have hmono : conjSub v R ≤ conjSub v (conjSub h0⁻¹ K) :=
        Work.BSW.S3.conjSub_mono hRK v
      rw [hvconjR] at hmono
      rwa [Work.BSW.S3.conjSub_conjSub] at hmono
    have hinf : conjSub h0⁻¹ K ⊓ conjSub (v * h0⁻¹) K ≠ ⊥ := by
      intro hbot
      exact hRne (le_bot_iff.mp (hbot ▸ le_inf hRK hle2))
    have hconjK : conjSub (v * h0⁻¹) K = conjSub h0⁻¹ K :=
      (conjSub_K_inf_eq_of_ne_bot (Work.BSW.S3.hyps (h := h)) hinf).symm
    have hvN : v ∈ Subgroup.normalizer ((conjSub h0⁻¹ K : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      show conjSub v (conjSub h0⁻¹ K) = conjSub h0⁻¹ K
      rw [Work.BSW.S3.conjSub_conjSub]
      exact hconjK
    have hvH : v ∈ conjSub h0⁻¹ (Subgroup.centralizer ({t} : Set G)) := by
      have h2 := hvN
      rw [Work.BSW.S3.normalizer_conjSub,
        Work.BSW.Api.normalizer_K_eq (Work.BSW.S3.hyps (h := h))] at h2
      exact h2
    exact mem_conjSub_K_of_mem_conjSub_centralizer_t_of_odd (Work.BSW.S3.hyps (h := h)) hvH hvodd
  · -- `w` is conjugate into `F = C_G(x)`
    have hwF : w ∈ conjSub g0⁻¹ (Subgroup.centralizer ({x} : Set G)) := by
      rw [Work.BSW.S3.mem_conjSub_iff]
      simpa using hg0
    refine Or.inr ⟨g0⁻¹, ?_⟩
    -- `R ≤ conjSub g0⁻¹ F`
    have hRF : R ≤ conjSub g0⁻¹ (Subgroup.centralizer ({x} : Set G)) := by
      intro u hu
      have hcomm : u * w = w * u := hwcenter u hu
      have hcw : u ∈ Subgroup.centralizer ({w} : Set G) := by
        rwa [Subgroup.mem_centralizer_singleton_iff]
      have hEq := Work.BSW.S3.centralizer_eq_of_mem_conjSub_centralizer_x h hwF hw1
      rw [hEq] at hcw
      exact hcw
    intro v hv
    rw [Subgroup.mem_inf] at hv
    obtain ⟨hvX, hvR⟩ := hv
    have hvodd : Odd (orderOf v) :=
      Odd.of_dvd_nat hNodd (Subgroup.orderOf_dvd_natCard _ hvX)
    have hvconjR : conjSub v R = R := Subgroup.mem_normalizer_iff_map_conj_eq.mp hvR
    have hle2 : R ≤ conjSub (v * g0⁻¹) (Subgroup.centralizer ({x} : Set G)) := by
      have hmono : conjSub v R ≤
          conjSub v (conjSub g0⁻¹ (Subgroup.centralizer ({x} : Set G))) :=
        Work.BSW.S3.conjSub_mono hRF v
      rw [hvconjR] at hmono
      rwa [Work.BSW.S3.conjSub_conjSub] at hmono
    have hinf : conjSub g0⁻¹ (Subgroup.centralizer ({x} : Set G)) ⊓
        conjSub (v * g0⁻¹) (Subgroup.centralizer ({x} : Set G)) ≠ ⊥ := by
      intro hbot
      exact hRne (le_bot_iff.mp (hbot ▸ le_inf hRF hle2))
    have hconjF : conjSub (v * g0⁻¹) (Subgroup.centralizer ({x} : Set G)) =
        conjSub g0⁻¹ (Subgroup.centralizer ({x} : Set G)) :=
      (conjSub_F_inf_eq_of_ne_bot h hinf).symm
    have hvN : v ∈ Subgroup.normalizer
        ((conjSub g0⁻¹ (Subgroup.centralizer ({x} : Set G)) : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      show conjSub v (conjSub g0⁻¹ (Subgroup.centralizer ({x} : Set G))) =
        conjSub g0⁻¹ (Subgroup.centralizer ({x} : Set G))
      rw [Work.BSW.S3.conjSub_conjSub]
      exact hconjF
    have hvM : v ∈ conjSub g0⁻¹
        (Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G)) : Set G)) := by
      have h2 := hvN
      rwa [Work.BSW.S3.normalizer_conjSub] at h2
    exact mem_conjSub_centralizer_x_of_mem_conjSub_normalizer_of_odd h hvM hvodd

end Work.BSW.BSW36
