import Mathlib
import Submission.Work.ThmF.ChV12.L6basic
import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.RankOneUniqueness.exists_smul_t_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.eq_one_of_centralizes_Q` — `D` acts faithfully on `Q`

If `d ∈ D = twoPoint H t` centralises `Q` then `d = 1`.  (Peterfalvi II Ch. V §2 Lemma 1 (c)
identifies `C_D(Q)` with the kernel `𝒩(G)`; here the kernel is shown to be trivial directly.)

`d` fixes `∞ = H` (as `d ∈ H`) and every point of `Ω = G ⧸ H`: for `a ∈ H` the element
`a⁻¹ d a` is conjugate into `H^t` — writing `a = q d'` with `q ∈ Q`, `d' ∈ D` it is `d'⁻¹ d d'`,
and `t (d'⁻¹ d d') t = (t d' t)⁻¹ (t d t) (t d' t) ∈ H`.  Hence `d` lies in the kernel of the
action on `Ω`, which is contained in `H ⊓ H^x` for any `x ∉ H`, hence has odd order, hence is
trivial (`oddCore G = ⊥`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open LeanEval.GroupTheory.Defs

namespace Work.ThmF.ChV12

open Submission.Blueprint Work.ThmF Work.RankOneUniqueness

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}

/-- If `H ≠ ⊤` there is `x ∉ H`. -/
theorem exists_notMem_of_ne_top {H : Subgroup G} (hH : H ≠ ⊤) : ∃ x : G, x ∉ H := by
  by_contra h
  push_neg at h
  exact hH (Subgroup.eq_top_iff' H |>.mpr h)

/-- **`C_D(Q) = 1`.**  An element of `D = twoPoint H t` centralising `Q` is trivial. -/
theorem eq_one_of_centralizes_Q (hS : Situation G) (h : IsSplitRankOne H Q t) {d : G}
    (hd : d ∈ twoPoint H t) (hdc : ∀ q ∈ Q, d * q = q * d) : d = 1 := by
  classical
  have h2 : t * t = 1 := mul_self_eq_one h
  have htinv : t⁻¹ = t := inv_eq_self h
  -- (0) `d ∈ conj t H`; transports between `conj t H` and `H`
  have hdconj : d ∈ conj t H := (mem_twoPoint_iff.mp hd).2
  have htmem : ∀ y ∈ conj t H, t * y * t ∈ H := by
    intro y hy
    obtain ⟨e, he, hey⟩ := (mem_conj_iff H t y).mp hy
    rw [← hey]
    rw [involution_conj h2]
    exact he
  have htt : ∀ y : G, t * (t * y * t) * t = y := fun y => by
    simpa [htinv] using involution_conj (e := y) h2
  have hdt : t * d * t ∈ H := htmem d hdconj
  -- (1) for `a ∈ H`, `a⁻¹ d a ∈ conj t H`
  have hmemconj : ∀ a ∈ H, a⁻¹ * d * a ∈ conj t H := by
    intro a ha
    obtain ⟨q, hq, d', hd', haqd⟩ := fact_exists h ha
    have hcomm : d * q = q * d := hdc q hq
    have hd'conj : d' ∈ conj t H := (mem_twoPoint_iff.mp hd').2
    have hq : q⁻¹ * d * q = d := by
      rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
    have hconj : a⁻¹ * d * a = d'⁻¹ * d * d' := by
      calc a⁻¹ * d * a = (q * d')⁻¹ * d * (q * d') := by rw [haqd]
        _ = d'⁻¹ * (q⁻¹ * d * q) * d' := by group
        _ = d'⁻¹ * d * d' := by rw [hq]
    rw [hconj]
    refine (mem_conj_iff H t (d'⁻¹ * d * d')).mpr
      ⟨t * (d'⁻¹ * d * d') * t, htmem _ ?_, ?_⟩
    · exact (conj t H).mul_mem ((conj t H).mul_mem ((conj t H).inv_mem hd'conj) hdconj) hd'conj
    · rw [htinv]
      exact htt (d'⁻¹ * d * d')
  -- (2) hence `(a⁻¹ d a) • (t • ∞) = t • ∞`
  have hfixmem : ∀ a ∈ H, (a⁻¹ * d * a) • (t • pt H) = t • pt H := by
    intro a ha
    obtain ⟨e, he, hed⟩ := (mem_conj_iff H t (a⁻¹ * d * a)).mp (hmemconj a ha)
    rw [← hed]
    calc (t * e * t⁻¹) • (t • pt H)
        = t • (e • (t⁻¹ • (t • pt H))) := by rw [mul_smul, mul_smul]
      _ = t • (e • pt H) := by
            rw [show t⁻¹ • (t • pt H) = pt H from
              by rw [← mul_smul, inv_mul_cancel, one_smul]]
      _ = t • pt H := by rw [smul_pt_of_mem H he]
  -- (3) `d` fixes every point of `Ω`
  have hfix : ∀ ω : G ⧸ H, d • ω = ω := by
    intro ω
    by_cases hω : ω = pt H
    · subst hω
      exact smul_pt_of_mem H (mem_twoPoint_iff.mp hd).1
    · obtain ⟨a, ha, haω⟩ := exists_smul_t_eq h hω
      rw [← haω]
      calc d • (a • (t • pt H))
          = (d * a) • (t • pt H) := by rw [mul_smul]
        _ = (a * (a⁻¹ * d * a)) • (t • pt H) := by
              rw [show d * a = a * (a⁻¹ * d * a) by group]
        _ = a • ((a⁻¹ * d * a) • (t • pt H)) := by rw [mul_smul]
        _ = a • (t • pt H) := by rw [hfixmem a ha]
  -- (4) `d ∈ ⋂_g conj g H = normalCore H`
  have hmem : ∀ g : G, d ∈ conj g H := by
    intro g
    have h1 : (g⁻¹ * d * g) • pt H = pt H := by
      have h0 : d • (g • pt H) = g • pt H := hfix (g • pt H)
      calc (g⁻¹ * d * g) • pt H
          = g⁻¹ • (d • (g • pt H)) := by rw [mul_smul, mul_smul]
        _ = g⁻¹ • (g • pt H) := by rw [h0]
        _ = (g⁻¹ * g) • pt H := by rw [← mul_smul]
        _ = pt H := by rw [inv_mul_cancel, one_smul]
    have h3 : g⁻¹ * d * g ∈ H := mem_of_smul_pt H h1
    rw [mem_conj_iff]
    exact ⟨g⁻¹ * d * g, h3, by group⟩
  have hdle : d ∈ benderKernel H := by
    have hker : Subgroup.zpowers d ≤ benderKernel H := by
      rw [le_benderKernel_iff]
      intro g
      exact Subgroup.zpowers_le.mpr (hmem g)
    exact hker (Subgroup.mem_zpowers d)
  -- (5) `normalCore H` has odd order, hence is trivial
  obtain ⟨x, hx⟩ := exists_notMem_of_ne_top h.stronglyEmbedded.1
  have hle2 : benderKernel H ≤ conj x H := by
    rw [benderKernel_eq_iInf]; exact iInf_le _ x
  have hle1 : benderKernel H ≤ H ⊓ conj x H :=
    fun y hy => ⟨benderKernel_le H hy, hle2 hy⟩
  have hoddN : Odd (Nat.card ↥(benderKernel H)) :=
    (h.stronglyEmbedded.2.2 x hx).of_dvd_nat (Subgroup.card_dvd_of_le hle1)
  have hNle : benderKernel H ≤ oddCore G :=
    le_sSup ⟨benderKernel_normal H, hoddN⟩
  have hcore : benderKernel H ≤ (⊥ : Subgroup G) := by
    rw [← hS.2.2]; exact hNle
  exact Subgroup.mem_bot.mp (hcore hdle)

end Work.ThmF.ChV12
