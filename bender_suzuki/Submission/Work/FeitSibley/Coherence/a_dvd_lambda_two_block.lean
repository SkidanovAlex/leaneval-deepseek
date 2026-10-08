import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab
import Submission.Work.FeitSibley.Coherence.engine
import Submission.Work.FeitSibley.Coherence.irr_congr_mod_card_Q
import Submission.Work.FeitSibley.Coherence.FSZ_aux
import Submission.Work.FeitSibley.Coherence.inf_H_conj_Q_eq_bot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence.a_dvd_lambda_two_block`

Peterfalvi II, Appendice XII, step (8): the divisibility `a ∣ λ` which concludes the two-block
argument.  With `𝒳 = 𝒮 ∖ 𝒮(Z)` (`Z = FSZ h = [Q₁,Q₁] ∩ Z(Q₁)`), `𝒴 = 𝒮(Q')`, `x₀ ∈ 𝒳` of
degree `a·|D|`, `y₀ ∈ 𝒴` (of degree `|D|`), a coherent extension `σ` of `𝒳` agreeing with
`Ind_H^G` on `ℤ[𝒳]⁰`, a coherent extension `ρ` of `𝒴`, and the "first equation" of step (6)
`⟨Ind(x₀ - a·y₀), ρ y⟩ = λ` (`y ≠ y₀`) resp. `λ - a` (`y = y₀`), one has `a ∣ λ`.

The proof is the one in the source (step (8) + step (7)):

* `ρ y₀` is `±` an irreducible `θ` of `G` (norm one virtual character);
* for `χ ∈ 𝒳`, writing `χ(1) = k·x₀(1)`, the orthogonality of the two blocks (`horth`) and the
  fact that `σ` agrees with `Ind` on `ℤ[𝒳]⁰` give `⟨Ind χ, ρ y₀⟩ = k·⟨Ind x₀, ρ y₀⟩`;
* expanding `Res_H^G (ρ y₀)` in `Irr H` and using `Z ≤ ker χ` for `χ ∉ 𝒳`, together with the
  regular-character identity `∑_{χ∈𝒳} χ(1)(χ(z) - χ(1)) = -|H|`, one gets
  `(ρ y₀)(z) - (ρ y₀)(1) = -⟨Ind x₀, ρ y₀⟩·|Q|/a` for `z ∈ Z^#`;
* hence `ρ y₀` is constant on `Z^#`, and step (7) (`irr_congr_mod_card_Q`) makes
  `⟨Ind x₀, ρ y₀⟩/a` a rational algebraic integer, so `a ∣ ⟨Ind x₀, ρ y₀⟩`;
* the first equation at `y₀` is `λ - a = ⟨Ind x₀, ρ y₀⟩ - a·⟨Ind y₀, ρ y₀⟩`, whence `a ∣ λ`.
-/

set_option maxHeartbeats 1000000

namespace Work.FeitSibley.Coherence

open Classical

noncomputable section

variable {G : Type} [Group G] [Fintype G]

/-- `𝒳 = 𝒮 ∖ 𝒮(Z)`, Peterfalvi's set of exceptional characters. -/
private abbrev FSX (h : Work.FeitSibley.FSData G) : Finset (↥h.H → ℂ) :=
  Work.FeitSibley.scriptS h.H h.Q1 \ Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h)

/-- `𝒴 = 𝒮(Q')`, Peterfalvi's set of characters trivial on `Q'`. -/
private abbrev FSY (h : Work.FeitSibley.FSData G) : Finset (↥h.H → ℂ) :=
  Work.FeitSibley.scriptSR h.H h.Q1 (FSQcomm h)

/-- An irreducible character of `H` which is not in `𝒳 = 𝒮 ∖ 𝒮(Z)` is trivial on `Z`. -/
private theorem irr_notMem_sdiff_FSZ_apply (h : Work.FeitSibley.FSData G) {χ : ↥h.H → ℂ}
    (hχ : χ ∈ Work.CharCore.Irr ↥h.H) (hχX : χ ∉ FSX h) {x : ↥h.H}
    (hx : (x : G) ∈ FSZ h) : χ x = χ 1 := by
  by_cases hχS : χ ∈ Work.FeitSibley.scriptS h.H h.Q1
  · have hχZ : χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSZ h) := by
      by_contra hc
      exact hχX (Finset.mem_sdiff.mpr ⟨hχS, hc⟩)
    exact (Work.FeitSibley.Coherence.mem_scriptSR_iff h (FSZ h)).mp hχZ |>.2 x hx
  · have hall : ∀ y : ↥h.H, (y : G) ∈ h.Q1 → χ y = χ 1 := by
      intro y hy
      by_contra hc
      exact hχS (Finset.mem_filter.mpr ⟨hχ, ⟨y, hy, hc⟩⟩)
    exact hall x (FSZ_le_Q1_aux h hx)

/-- **The evaluation identity of step (8).**  For a class function `ψ` on `G`, the difference of
the values of `Res_H^G ψ` at `z ∈ Z` and at `1` is the sum of the `𝒳`-components of `Res_H^G ψ`
weighted by `χ(z) - χ(1)`: every irreducible of `H` outside `𝒳` is trivial on `Z`. -/
private theorem resFun_sub_eq_sum_sdiff_FSZ (h : Work.FeitSibley.FSData G)
    {ψ : G → ℂ} (hψ : Work.CharCore.IsClassFun ψ)
    {z : G} (hz : z ∈ FSZ h) :
    Work.CharCore.resFun h.H ψ ⟨z, FSZ_le_H_aux h hz⟩ - Work.CharCore.resFun h.H ψ 1
      = ∑ χ ∈ FSX h,
          (Work.CharCore.cfInner (Work.CharCore.resFun h.H ψ) χ) *
            (χ ⟨z, FSZ_le_H_aux h hz⟩ - χ 1) := by
  classical
  set Φ : ↥h.H → ℂ := Work.CharCore.resFun h.H ψ with hΦ
  have hΦclass : Work.CharCore.IsClassFun Φ := fun g k => hψ g k
  have hexp := Work.CharCore.classFun_eq_sum_irr hΦclass
  have hXsub : FSX h ⊆ Work.CharCore.Irr ↥h.H := by
    intro χ hχ
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hχ).1).1
  have hzval : Φ ⟨z, FSZ_le_H_aux h hz⟩ =
      ∑ χ ∈ Work.CharCore.Irr ↥h.H,
        (Work.CharCore.cfInner Φ χ) * χ ⟨z, FSZ_le_H_aux h hz⟩ := by
    conv_lhs => rw [hexp]
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun χ _ => by rw [Pi.smul_apply, smul_eq_mul]
  have h1val : Φ 1 =
      ∑ χ ∈ Work.CharCore.Irr ↥h.H, (Work.CharCore.cfInner Φ χ) * χ 1 := by
    conv_lhs => rw [hexp]
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun χ _ => by rw [Pi.smul_apply, smul_eq_mul]
  have hIrr : (∑ χ ∈ Work.CharCore.Irr ↥h.H,
        (Work.CharCore.cfInner Φ χ) * (χ ⟨z, FSZ_le_H_aux h hz⟩ - χ 1))
      = (∑ χ ∈ Work.CharCore.Irr ↥h.H,
            (Work.CharCore.cfInner Φ χ) * χ ⟨z, FSZ_le_H_aux h hz⟩)
        - (∑ χ ∈ Work.CharCore.Irr ↥h.H, (Work.CharCore.cfInner Φ χ) * χ 1) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun χ _ => by ring
  have hzero : (∑ χ ∈ (Work.CharCore.Irr ↥h.H \ FSX h),
        (Work.CharCore.cfInner Φ χ) * (χ ⟨z, FSZ_le_H_aux h hz⟩ - χ 1)) = 0 := by
    refine Finset.sum_eq_zero fun χ hχ => ?_
    rw [Finset.mem_sdiff] at hχ
    rw [irr_notMem_sdiff_FSZ_apply h hχ.1 hχ.2 hz, sub_self, mul_zero]
  have hsdiff := Finset.sum_sdiff (s₁ := FSX h) (s₂ := Work.CharCore.Irr ↥h.H)
    (f := fun χ : ↥h.H → ℂ =>
      (Work.CharCore.cfInner Φ χ) * (χ ⟨z, FSZ_le_H_aux h hz⟩ - χ 1)) hXsub
  show Φ ⟨z, FSZ_le_H_aux h hz⟩ - Φ 1
      = ∑ χ ∈ FSX h, (Work.CharCore.cfInner Φ χ) * (χ ⟨z, FSZ_le_H_aux h hz⟩ - χ 1)
  rw [hzval, h1val, ← hIrr, ← hsdiff, hzero, zero_add]

/-- **The orthogonality relation of step (5)/(8).**  If `χ ∈ 𝒳` has `χ(1) = k·x₀(1)`, then
`⟨Ind_H^G χ, ρ y⟩ = k·⟨Ind_H^G x₀, ρ y⟩` for every `y ∈ 𝒴`: `χ - k·x₀ ∈ ℤ[𝒳]⁰`, so `σ` agrees
with `Ind_H^G` there, and both `σ χ` and `σ x₀` are orthogonal to `ρ y`. -/
private theorem cfInner_indLin_sdiff_FSZ (h : Work.FeitSibley.FSData G) {x₀ : ↥h.H → ℂ}
    (hx₀ : x₀ ∈ FSX h)
    {σ ρ : (↥h.H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hσ0 : ∀ α ∈ Work.Coherence.ZSpan0 (FSX h), σ α = Work.FeitSibley.indLin h.H α)
    (horth : ∀ χ ∈ FSX h, ∀ y ∈ FSY h, Work.CharCore.cfInner (σ χ) (ρ y) = 0)
    {χ : ↥h.H → ℂ} (hχ : χ ∈ FSX h) {y : ↥h.H → ℂ} (hy : y ∈ FSY h)
    {k : ℤ} (hk : χ 1 = (k : ℂ) * (x₀ 1)) :
    Work.CharCore.cfInner (Work.FeitSibley.indLin h.H χ) (ρ y)
      = (k : ℂ) * Work.CharCore.cfInner (Work.FeitSibley.indLin h.H x₀) (ρ y) := by
  classical
  set u : ↥h.H → ℂ := χ - (k : ℂ) • x₀ with hu
  have hu_mem : u ∈ Work.Coherence.ZSpan (FSX h) := by
    rw [hu]
    rw [show ((k : ℂ) • x₀ : ↥h.H → ℂ) = (k : ℤ) • x₀ from Int.cast_smul_eq_zsmul ℂ k x₀]
    exact AddSubgroup.sub_mem _ (Work.Coherence.self_mem_zSpan hχ)
      (AddSubgroup.zsmul_mem _ (Work.Coherence.self_mem_zSpan hx₀) k)
  have hu_zero : u 1 = 0 := by
    rw [hu]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hk]
    ring
  have huZ : u ∈ Work.Coherence.ZSpan0 (FSX h) := ⟨hu_mem, hu_zero⟩
  have hσu : σ u = Work.FeitSibley.indLin h.H u := hσ0 u huZ
  have hdecomp : (χ : ↥h.H → ℂ) = (k : ℂ) • x₀ + u := by
    rw [hu]
    ext t
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hσχ : σ χ = (k : ℂ) • σ x₀ + Work.FeitSibley.indLin h.H u := by
    rw [show (χ : ↥h.H → ℂ) = (k : ℂ) • x₀ + u from hdecomp, map_add]
    congr 1
    rw [show ((k : ℂ) • x₀ : ↥h.H → ℂ) = (k : ℤ) • x₀ from Int.cast_smul_eq_zsmul ℂ k x₀]
    rw [map_smul]
    exact (Int.cast_smul_eq_zsmul ℂ k (σ x₀)).symm
  have hind : Work.FeitSibley.indLin h.H u
      = Work.FeitSibley.indLin h.H χ - (k : ℂ) • Work.FeitSibley.indLin h.H x₀ := by
    rw [hu, show (χ - (k : ℂ) • x₀ : ↥h.H → ℂ) = χ - (k : ℤ) • x₀ from by
      rw [Int.cast_smul_eq_zsmul]]
    rw [map_sub, map_smul]
    rw [show ((k : ℤ) • Work.FeitSibley.indLin h.H x₀ : G → ℂ)
        = (k : ℂ) • Work.FeitSibley.indLin h.H x₀
        from (Int.cast_smul_eq_zsmul ℂ k _).symm]
  have hterm : Work.CharCore.cfInner (σ χ) (ρ y)
      = (k : ℂ) * Work.CharCore.cfInner (σ x₀) (ρ y)
        + Work.CharCore.cfInner (Work.FeitSibley.indLin h.H u) (ρ y) := by
    rw [hσχ, Work.CharCore.cfInner_add_left, Work.CharCore.cfInner_smul_left]
  have h0 : Work.CharCore.cfInner (Work.FeitSibley.indLin h.H u) (ρ y) = 0 := by
    have h1 := horth χ hχ y hy
    have h2 := horth x₀ hx₀ y hy
    rw [h1, h2] at hterm
    simpa using hterm.symm
  have hlin : Work.CharCore.cfInner (Work.FeitSibley.indLin h.H u) (ρ y)
      = Work.CharCore.cfInner (Work.FeitSibley.indLin h.H χ) (ρ y)
        - (k : ℂ) * Work.CharCore.cfInner (Work.FeitSibley.indLin h.H x₀) (ρ y) := by
    rw [hind, Work.CharCore.cfInner_sub_left, Work.CharCore.cfInner_smul_left]
  have hkey : Work.CharCore.cfInner (Work.FeitSibley.indLin h.H χ) (ρ y)
      - (k : ℂ) * Work.CharCore.cfInner (Work.FeitSibley.indLin h.H x₀) (ρ y) = 0 := by
    rw [← hlin, h0]
  exact sub_eq_zero.mp hkey

/-- **The regular-character rescaling of step (8).**  The `1/(a·|D|)`-weighted sum of
`χ(1)·(χ(z) - χ(1))` over `𝒳` equals `-|H|/(a·|D|)`. -/
private theorem sum_one_div_sdiff_FSZ (h : Work.FeitSibley.FSData G) (a : ℕ) {z : G}
    (hz : z ∈ FSZ h) (hz1 : z ≠ 1) :
    (∑ χ ∈ FSX h, (1 / ((a : ℂ) * (Nat.card h.D : ℂ))) *
        ((χ 1) * (χ ⟨z, FSZ_le_H_aux h hz⟩ - χ 1)))
      = (1 / ((a : ℂ) * (Nat.card h.D : ℂ))) * (-(Nat.card h.H : ℂ)) := by
  classical
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_congr rfl (fun χ (_ : χ ∈ FSX h) =>
    (by ring : (χ 1) * (χ ⟨z, FSZ_le_H_aux h hz⟩ - χ 1)
      = (χ 1) * χ ⟨z, FSZ_le_H_aux h hz⟩ - (χ 1) * χ 1))]
  rw [Finset.sum_sub_distrib]
  exact sum_deg_chi_sdiff_FSZ_aux h hz hz1

theorem a_dvd_lambda_two_block {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpg : IsPGroup p h.Q1)
    (hab : ⁅h.Q1, h.Q1⁆ ≠ ⊥) (hQhall : Nat.Coprime (Nat.card h.Q) h.Q.index)
    {x₀ y₀ : ↥h.H → ℂ}
    (hx₀ : x₀ ∈ (Work.FeitSibley.scriptS h.H h.Q1 \
        Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSZ h)))
    (hy₀ : y₀ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSQcomm h))
    {a : ℕ} (ha : a ≠ 0) (hx₀deg : x₀ 1 = (a : ℂ) * (Nat.card h.D : ℂ))
    (hdegX : ∀ χ ∈ (Work.FeitSibley.scriptS h.H h.Q1 \
        Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSZ h)),
        ∃ k : ℤ, χ 1 = (k : ℂ) * (x₀ 1))
    {σ ρ : (↥h.H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hσ0 : ∀ α ∈ Work.Coherence.ZSpan0 (Work.FeitSibley.scriptS h.H h.Q1 \
        Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSZ h)),
        σ α = Work.FeitSibley.indLin h.H α)
    (horth : ∀ χ ∈ (Work.FeitSibley.scriptS h.H h.Q1 \
        Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSZ h)),
        ∀ y ∈ Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSQcomm h),
        Work.Coherence.cfInner (σ χ) (ρ y) = 0)
    (hρV : Work.Coherence.IsVChar (ρ y₀))
    (hρ1 : Work.Coherence.cfInner (ρ y₀) (ρ y₀) = 1)
    {c : ℤ}
    (hc : ∀ y ∈ Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSQcomm h),
        Work.Coherence.cfInner
          (Work.FeitSibley.indLin h.H (x₀ - (a : ℂ) • y₀)) (ρ y)
          = if y = y₀ then (c : ℂ) - (a : ℂ) else (c : ℂ)) :
    (a : ℤ) ∣ c := by
  classical
  -- normalise the `cfInner` occurrences to the `CharCore` version
  simp only [Work.CharCore.cfInner_coherence] at hρ1 horth hc
  have hx₀X : x₀ ∈ FSX h := hx₀
  have hy₀Y : y₀ ∈ FSY h := hy₀
  have hσ0X : ∀ α ∈ Work.Coherence.ZSpan0 (FSX h), σ α = Work.FeitSibley.indLin h.H α := hσ0
  have horthX : ∀ χ ∈ FSX h, ∀ y ∈ FSY h, Work.CharCore.cfInner (σ χ) (ρ y) = 0 := horth
  have hcY : ∀ y ∈ FSY h, Work.CharCore.cfInner
      (Work.FeitSibley.indLin h.H (x₀ - (a : ℂ) • y₀)) (ρ y)
      = if y = y₀ then (c : ℂ) - (a : ℂ) else (c : ℂ) := hc
  have hdegXX : ∀ χ ∈ FSX h, ∃ k : ℤ, χ 1 = (k : ℂ) * (x₀ 1) := hdegX
  -- `ψ = ρ y₀` is `±` an irreducible character of `G`
  have hψV : Work.CharCore.IsVChar (ρ y₀) := (Work.CharCore.IsVChar_iff_coherence _).mpr hρV
  have hψ1 : Work.CharCore.cfInner (ρ y₀) (ρ y₀) = 1 := hρ1
  obtain ⟨θ, hθ, hθcase⟩ := Work.CharCore.vchar_norm_one hψV hψ1
  have hψclass : Work.CharCore.IsClassFun (ρ y₀) := hψV.isClassFun
  -- integrality of the two relevant inner products
  have hx₀S : x₀ ∈ Work.FeitSibley.scriptS h.H h.Q1 := (Finset.mem_sdiff.mp hx₀).1
  have hy₀S : y₀ ∈ Work.FeitSibley.scriptS h.H h.Q1 := scriptSR_subset_scriptS h _ hy₀
  obtain ⟨Mx, hMx⟩ : ∃ M : ℤ,
      Work.CharCore.cfInner (Work.FeitSibley.indLin h.H x₀) (ρ y₀) = (M : ℂ) :=
    Work.CharCore.cfInner_int_vchar
      ((Work.CharCore.IsVChar_iff_coherence _).mpr (isVChar_indLin_scriptS h hx₀S)) hψV
  obtain ⟨My, hMy⟩ : ∃ M : ℤ,
      Work.CharCore.cfInner (Work.FeitSibley.indLin h.H y₀) (ρ y₀) = (M : ℂ) :=
    Work.CharCore.cfInner_int_vchar
      ((Work.CharCore.IsVChar_iff_coherence _).mpr (isVChar_indLin_scriptS h hy₀S)) hψV
  -- the coefficient relation on `𝒳`
  have hrel : ∀ χ ∈ FSX h, ∀ k : ℤ, χ 1 = (k : ℂ) * (x₀ 1) →
      Work.CharCore.cfInner (Work.CharCore.resFun h.H (ρ y₀)) χ
        = (k : ℂ) * Work.CharCore.cfInner (Work.CharCore.resFun h.H (ρ y₀)) x₀ := by
    intro χ hχ k hk
    have h1 := cfInner_indLin_sdiff_FSZ h hx₀X hσ0X horthX hχ hy₀Y hk
    have h2 : Work.CharCore.cfInner (Work.FeitSibley.indLin h.H χ) (ρ y₀)
        = Work.CharCore.cfInner χ (Work.CharCore.resFun h.H (ρ y₀)) :=
      Work.Induction.frobenius_reciprocity h.H χ (ρ y₀) hψclass
    have h3 : Work.CharCore.cfInner (Work.FeitSibley.indLin h.H x₀) (ρ y₀)
        = Work.CharCore.cfInner x₀ (Work.CharCore.resFun h.H (ρ y₀)) :=
      Work.Induction.frobenius_reciprocity h.H x₀ (ρ y₀) hψclass
    rw [Work.CharCore.cfInner_conj_symm (Work.CharCore.resFun h.H (ρ y₀)) χ, ← h2, h1, h3,
      Work.CharCore.cfInner_conj_symm (Work.CharCore.resFun h.H (ρ y₀)) x₀]
    simp only [starRingEnd_apply, star_mul', star_intCast]
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hDC : (Nat.card h.D : ℂ) ≠ 0 := by
    haveI : Nonempty ↥h.D := ⟨⟨1, h.D.one_mem⟩⟩
    exact_mod_cast Nat.card_pos.ne'
  have hQnz : (Nat.card h.Q : ℂ) ≠ 0 := by
    haveI : Nonempty ↥h.Q := ⟨⟨1, h.Q.one_mem⟩⟩
    exact_mod_cast Nat.card_pos.ne'
  have hcx₀ : Work.CharCore.cfInner (Work.CharCore.resFun h.H (ρ y₀)) x₀ = (Mx : ℂ) := by
    rw [Work.CharCore.cfInner_conj_symm (Work.CharCore.resFun h.H (ρ y₀)) x₀]
    have h3 : Work.CharCore.cfInner x₀ (Work.CharCore.resFun h.H (ρ y₀))
        = Work.CharCore.cfInner (Work.FeitSibley.indLin h.H x₀) (ρ y₀) :=
      (Work.Induction.frobenius_reciprocity h.H x₀ (ρ y₀) hψclass).symm
    rw [h3, hMx]
    exact map_intCast (starRingEnd ℂ) Mx
  have hHcard : (Nat.card h.H : ℂ) = (Nat.card h.Q : ℂ) * (Nat.card h.D : ℂ) := by
    rw [card_H_eq_card_Q_mul_card_D h, Nat.cast_mul]
  -- the value of `ρ y₀` on `Z^#`
  have hval : ∀ (z : G) (hz : z ∈ FSZ h), z ≠ 1 →
      Work.CharCore.resFun h.H (ρ y₀) ⟨z, FSZ_le_H_aux h hz⟩
        - Work.CharCore.resFun h.H (ρ y₀) 1
      = -((Mx : ℂ) * (Nat.card h.Q : ℂ) / (a : ℂ)) := by
    intro z hz hz1
    rw [resFun_sub_eq_sum_sdiff_FSZ h hψclass hz]
    have hterm : ∀ χ ∈ FSX h,
        (Work.CharCore.cfInner (Work.CharCore.resFun h.H (ρ y₀)) χ) *
            (χ ⟨z, FSZ_le_H_aux h hz⟩ - χ 1)
        = (Work.CharCore.cfInner (Work.CharCore.resFun h.H (ρ y₀)) x₀) *
            ((1 / ((a : ℂ) * (Nat.card h.D : ℂ))) *
              ((χ 1) * (χ ⟨z, FSZ_le_H_aux h hz⟩ - χ 1))) := by
      intro χ hχ
      obtain ⟨k, hk⟩ := hdegXX χ hχ
      rw [hrel χ hχ k hk]
      have hkC : (k : ℂ) = (χ 1) / ((a : ℂ) * (Nat.card h.D : ℂ)) := by
        rw [hk, hx₀deg]
        field_simp
      rw [hkC]
      ring
    rw [Finset.sum_congr rfl hterm]
    rw [← Finset.mul_sum]
    rw [sum_one_div_sdiff_FSZ h a hz hz1]
    rw [hcx₀, hHcard]
    field_simp
    try ring
  -- `ρ y₀` is constant on `Z^#`, so `θ` is too
  have hZne : FSZ h ≠ ⊥ := FSZ_ne_bot_aux h hp hpg hab
  have hZex : ∃ z : G, z ∈ FSZ h ∧ z ≠ 1 := by
    by_contra hcon
    apply hZne
    exact le_bot_iff.mp (fun x hx => by
      by_contra hx1
      exact hcon ⟨x, hx, hx1⟩)
  obtain ⟨z₀, hz₀, hz₀1⟩ := hZex
  have hconstψ : ∀ z ∈ FSZ h, z ≠ 1 → ∀ z' ∈ FSZ h, z' ≠ 1 → (ρ y₀) z = (ρ y₀) z' := by
    intro z hz hz1 z' hz' hz'1
    have e1 := hval z hz hz1
    have e2 := hval z' hz' hz'1
    have hsub : Work.CharCore.resFun h.H (ρ y₀) ⟨z, FSZ_le_H_aux h hz⟩
        - Work.CharCore.resFun h.H (ρ y₀) 1
        = Work.CharCore.resFun h.H (ρ y₀) ⟨z', FSZ_le_H_aux h hz'⟩
        - Work.CharCore.resFun h.H (ρ y₀) 1 := by rw [e1, e2]
    have hcancel : Work.CharCore.resFun h.H (ρ y₀) ⟨z, FSZ_le_H_aux h hz⟩
        = Work.CharCore.resFun h.H (ρ y₀) ⟨z', FSZ_le_H_aux h hz'⟩ := by
      rw [sub_eq_add_neg, sub_eq_add_neg] at hsub
      exact add_right_cancel hsub
    show (ρ y₀) z = (ρ y₀) z'
    exact hcancel
  have hconstθ : ∀ z ∈ FSZ h, z ≠ 1 → ∀ z' ∈ FSZ h, z' ≠ 1 → θ z = θ z' := by
    intro z hz hz1 z' hz' hz'1
    rcases hθcase with hcase | hcase
    · rw [← hcase]
      exact hconstψ z hz hz1 z' hz' hz'1
    · have hneg : θ = -(ρ y₀) := by rw [hcase]; simp
      rw [hneg]
      simp only [Pi.neg_apply]
      rw [hconstψ z hz hz1 z' hz' hz'1]
  have hZcent : ∀ z ∈ FSZ h, ∀ y ∈ h.Q1, z * y = y * z := by
    intro z hz y hy
    have hzc := (Subgroup.mem_inf.mp hz).2
    exact (Subgroup.mem_centralizer_iff.mp hzc y hy).symm
  have hintθ : IsIntegral ℤ ((θ z₀ - θ 1) / (Nat.card h.Q : ℂ)) :=
    irr_congr_mod_card_Q h (FSZ_le_H_aux h) (FSZ_le_Q1_aux h) (FSZ_normal_in_H_aux h) hZcent
      hZne hQhall (fun z hz hz1 g => FSZ_not_inv_aux h hp hp2 hpg hz hz1 g)
      hθ hconstθ z₀ hz₀ hz₀1
  have hintψ : IsIntegral ℤ (((ρ y₀) z₀ - (ρ y₀) 1) / (Nat.card h.Q : ℂ)) := by
    rcases hθcase with hcase | hcase
    · rw [hcase]
      exact hintθ
    · have hEq : ((ρ y₀) z₀ - (ρ y₀) 1) / (Nat.card h.Q : ℂ)
          = -((θ z₀ - θ 1) / (Nat.card h.Q : ℂ)) := by
        rw [hcase]
        simp only [Pi.neg_apply]
        ring
      rw [hEq]
      exact hintθ.neg
  have hintMx : IsIntegral ℤ (((-Mx : ℤ) : ℂ) / (a : ℂ)) := by
    have hEq : ((ρ y₀) z₀ - (ρ y₀) 1) / (Nat.card h.Q : ℂ) = -((Mx : ℂ) / (a : ℂ)) := by
      have hv := hval z₀ hz₀ hz₀1
      have hv' : (ρ y₀) z₀ - (ρ y₀) 1
          = -((Mx : ℂ) * (Nat.card h.Q : ℂ) / (a : ℂ)) := by
        show Work.CharCore.resFun h.H (ρ y₀) ⟨z₀, FSZ_le_H_aux h hz₀⟩
          - Work.CharCore.resFun h.H (ρ y₀) 1
          = -((Mx : ℂ) * (Nat.card h.Q : ℂ) / (a : ℂ))
        exact hv
      rw [hv']
      field_simp
      try ring
    rw [hEq] at hintψ
    convert hintψ using 1
    push_cast
    ring
  have hMxdvd : (a : ℤ) ∣ Mx := by
    have h := dvd_of_isIntegral_int_div ha hintMx
    exact dvd_neg.mp h
  -- the first equation at `y₀`
  have hcf : Work.CharCore.cfInner (Work.FeitSibley.indLin h.H (x₀ - (a : ℂ) • y₀)) (ρ y₀)
      = (Mx : ℂ) - (a : ℂ) * (My : ℂ) := by
    have hline : Work.FeitSibley.indLin h.H (x₀ - (a : ℂ) • y₀)
        = Work.FeitSibley.indLin h.H x₀ - (a : ℂ) • Work.FeitSibley.indLin h.H y₀ := by
      have hcast : ((a : ℂ) • y₀ : ↥h.H → ℂ) = (a : ℤ) • y₀ := by
        conv_lhs => rw [← Int.cast_natCast (R := ℂ) a]
        rw [Int.cast_smul_eq_zsmul]
      have hcast2 : ((a : ℤ) • Work.FeitSibley.indLin h.H y₀ : G → ℂ)
          = (a : ℂ) • Work.FeitSibley.indLin h.H y₀ := by
        conv_rhs => rw [← Int.cast_natCast (R := ℂ) a]
        rw [← Int.cast_smul_eq_zsmul (R := ℂ)]
      rw [show (x₀ - (a : ℂ) • y₀ : ↥h.H → ℂ) = x₀ - (a : ℤ) • y₀ from by rw [hcast]]
      rw [map_sub, map_smul, hcast2]
    rw [hline, Work.CharCore.cfInner_sub_left, Work.CharCore.cfInner_smul_left, hMx, hMy]
  have hceq : (c : ℂ) = ((Mx - (a : ℤ) * My + (a : ℤ) : ℤ) : ℂ) := by
    have hcy := hcY y₀ hy₀Y
    rw [if_pos rfl] at hcy
    rw [hcf] at hcy
    push_cast
    linear_combination -hcy
  have hcm : c = Mx - (a : ℤ) * My + (a : ℤ) := Int.cast_injective hceq
  obtain ⟨t, ht⟩ := hMxdvd
  refine ⟨t - My + 1, ?_⟩
  rw [hcm, ht]
  ring

end

end Work.FeitSibley.Coherence
