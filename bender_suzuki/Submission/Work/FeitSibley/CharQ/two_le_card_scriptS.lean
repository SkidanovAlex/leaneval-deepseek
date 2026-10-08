import Mathlib
import Submission.Work.FeitSibley.CharQ.Defs
import Submission.Work.FeitSibley.Basic
import Submission.Work.FeitSibley.CharQ.ScriptSAPI
import Submission.Work.FeitSibley.CharQ.orbit_two_irr
import Submission.Work.FeitSibley.CharQ.neq_of_not_conj
import Submission.Work.CharPrelim.ft4_5_aux
import Submission.Work.CharCore.Main
import Submission.Work.Clifford.Orbit
import Submission.Work.Clifford.clifford_correspondence

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.CharQ.two_le_card_scriptS`

`𝒮 = {χ ∈ Irr H | Q₁ ⊄ ker χ}` has at least two members.

The proof produces two *distinct* irreducible characters of `H` which are non-trivial on `Q₁`.
The group `A = D` acts fixed-point-freely on `Q₁` (`h.D_fpf_Q1`) with odd order (`h.D_odd`);
`orbit_two_irr` produces two non-trivial irreducible characters `θ₁, θ₂` of `Q₁` which are not
conjugate under this action, `Work.CharPrelim.exists_irr_constituent_indFun` lifts each `θᵢ` to
an irreducible `χᵢ` of `H` whose restriction to `Q₁` has `θᵢ` as a constituent, and the
constituent form of Clifford's theorem (`neq_of_not_conj`) shows `χ₁ ≠ χ₂`.
-/

noncomputable section

open Classical

namespace Work.FeitSibley.CharQ

theorem two_le_card_scriptS {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G) :
    2 ≤ (Work.FeitSibley.scriptS h.H h.Q1).card := by
  classical
  have hQ1n : (h.Q1.subgroupOf h.H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer h.Q1_normal_in_H
  let N : Subgroup ↥h.H := h.Q1.subgroupOf h.H
  have hNnorm : N.Normal := hQ1n
  letI : N.Normal := hNnorm
  let A : Subgroup ↥h.H := h.D.subgroupOf h.H
  -- the conjugation action of `A` on `N`
  let ρ : ↥A →* MulAut ↥N :=
    (MulAut.conjNormal (G := ↥h.H) (H := N)).comp (Subgroup.subtype A)
  have hAodd : Odd (Nat.card ↥A) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.D_le_H).toEquiv).symm ▸ h.D_odd
  have hnot2 : ¬ IsPGroup 2 ↥N := fun h2 =>
    h.Q1_not_two (IsPGroup.of_equiv h2 (Subgroup.subgroupOfEquivOfLe h.Q1_le_H))
  have hfpf : ∀ a : ↥A, a ≠ 1 → ∀ x : ↥N, ρ a x = x → x = 1 := by
    intro a ha x hx
    have haG : (((a : ↥A) : ↥h.H) : G) ≠ 1 := by
      intro hc
      exact ha (Subtype.ext (Subtype.ext hc))
    have hxA : (a : ↥h.H) * (x : ↥h.H) * (a : ↥h.H)⁻¹ = (x : ↥h.H) := by
      have h1 : ((ρ a x : ↥N) : ↥h.H) = (x : ↥h.H) :=
        congrArg (fun y : ↥N => (y : ↥h.H)) hx
      simpa [ρ, MulAut.conjNormal_apply] using h1
    have hxG : ((a : ↥h.H) : G) * (x : G) * ((a : ↥h.H) : G)⁻¹ = (x : G) := by
      have h1 := congrArg (fun y : ↥h.H => (y : G)) hxA
      simpa using h1
    exact Subtype.ext (Subtype.ext (h.D_fpf_Q1 ((a : ↥h.H) : G)
      (Subgroup.mem_subgroupOf.mp a.2) haG
      (x : G) (Subgroup.mem_subgroupOf.mp x.2) hxG))
  obtain ⟨θ₁, hθ₁Irr, θ₂, hθ₂Irr, hnt₁, hnt₂, hnotconjD⟩ :=
    orbit_two_irr (K := ↥N) ρ hAodd hfpf hnot2
  -- `θᵢ` is not the principal character
  have hθ₁ne : θ₁ ≠ (fun _ : ↥N => 1) := by
    obtain ⟨x, hx⟩ := hnt₁
    intro hc
    exact hx (by rw [hc])
  have hθ₂ne : θ₂ ≠ (fun _ : ↥N => 1) := by
    obtain ⟨x, hx⟩ := hnt₂
    intro hc
    exact hx (by rw [hc])
  -- `Q` acts trivially on `Irr N`
  have hQtriv : ∀ q : ↥h.H, (q : G) ∈ h.Q → Work.Clifford.conjFun N q θ₁ = θ₁ := by
    intro q hq
    obtain ⟨s, hs, b, hb, hqb⟩ := h.mem_Q_decomp hq
    let bN : ↥N := ⟨⟨b, h.Q1_le_H hb⟩, Subgroup.mem_subgroupOf.mpr hb⟩
    funext x
    rw [Work.Clifford.conjFun_apply]
    have hstep : (⟨q * x * q⁻¹, hNnorm.conj_mem x x.2 q⟩ : ↥N) = bN * x * bN⁻¹ := by
      apply Subtype.ext
      apply Subtype.ext
      show (q : G) * (x : G) * (q : G)⁻¹ =
        (((bN * x * bN⁻¹ : ↥N) : ↥h.H) : G)
      rw [hqb]
      have hcomm : s * (b * (x : G) * b⁻¹) = (b * (x : G) * b⁻¹) * s :=
        h.commute s hs _ (mul_mem (mul_mem hb (Subgroup.mem_subgroupOf.mp x.2)) (inv_mem hb))
      have hbNval : ((bN : ↥N) : ↥h.H) = ⟨b, h.Q1_le_H hb⟩ := rfl
      have hcalc : (((bN * x * bN⁻¹ : ↥N) : ↥h.H) : G) = b * (x : G) * b⁻¹ := by
        change (((bN : ↥N) : ↥h.H) : G) * (x : G) * (((bN : ↥N) : ↥h.H) : G)⁻¹ = _
        rw [hbNval]
      rw [hcalc]
      calc (s * b) * (x : G) * (s * b)⁻¹ = s * (b * (x : G) * b⁻¹) * s⁻¹ := by group
        _ = (b * (x : G) * b⁻¹) * s * s⁻¹ := by rw [hcomm]
        _ = b * (x : G) * b⁻¹ := by group
    rw [hstep]
    exact (Work.Clifford.IsClassFun.of_mem_Irr
      ((Work.Clifford.corr_mem_Irr_charCore (G := ↥N)).mpr hθ₁Irr)) x bN
  -- `θ₁` and `θ₂` are not `H`-conjugate
  have hnotconj : ¬ ∃ g : ↥h.H, Work.Clifford.conjFun N g θ₁ = θ₂ := by
    rintro ⟨g, hg⟩
    obtain ⟨q₀, hq₀, d₀, hd₀, hgd⟩ := h.mem_H_decomp g.2
    let dd : ↥A := ⟨⟨d₀, h.D_le_H hd₀⟩, hd₀⟩
    have hgq : g = (⟨q₀, h.Q_le_H hq₀⟩ : ↥h.H) * (dd : ↥h.H) := by
      apply Subtype.ext
      show (g : G) = q₀ * d₀
      exact hgd
    rw [hgq, Work.Clifford.conjFun_mul, hQtriv ⟨q₀, h.Q_le_H hq₀⟩ hq₀] at hg
    exact hnotconjD dd (by
      rw [← hg]
      funext x
      rw [Work.Clifford.conjFun_apply]
      have hρ : ρ dd = MulAut.conjNormal (G := ↥h.H) (H := N) (dd : ↥h.H) := rfl
      have harg : ρ dd x = (⟨(dd : ↥h.H) * x * (dd : ↥h.H)⁻¹,
          hNnorm.conj_mem x x.2 (dd : ↥h.H)⟩ : ↥N) := by
        rw [hρ]
        apply Subtype.ext
        rw [MulAut.conjNormal_apply]
      rw [harg])
  -- lift the two characters to `H`
  obtain ⟨χ₁, hχ₁Irr, hc₁⟩ :=
    Work.CharPrelim.exists_irr_constituent_indFun (G := ↥h.H) (N := N) hθ₁Irr
  obtain ⟨χ₂, hχ₂Irr, hc₂⟩ :=
    Work.CharPrelim.exists_irr_constituent_indFun (G := ↥h.H) (N := N) hθ₂Irr
  have hχne : χ₁ ≠ χ₂ :=
    neq_of_not_conj (N := N) hθ₁Irr hθ₂Irr hnotconj hχ₁Irr hχ₂Irr hc₁ hc₂
  -- each `χᵢ` is non-trivial on `Q₁`
  have hnt : ∀ {θ : ↥N → ℂ}, θ ∈ Work.CharCore.Irr ↥N → θ ≠ (fun _ : ↥N => 1) →
      ∀ {χ : ↥h.H → ℂ}, Work.CharCore.cfInner θ (Work.CharCore.resFun N χ) ≠ 0 →
      ∃ x : ↥h.H, (x : G) ∈ h.Q1 ∧ χ x ≠ χ 1 := by
    intro θ hθ hθne χ hc
    by_contra hcon
    push_neg at hcon
    have hres : Work.CharCore.resFun N χ = (χ 1) • (fun _ : ↥N => (1 : ℂ)) := by
      funext y
      simp only [Work.CharCore.resFun, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
      exact hcon (y : ↥h.H) y.2
    have horth : Work.CharCore.cfInner θ (fun _ : ↥N => (1 : ℂ)) = 0 := by
      rw [Work.CharCore.irr_orthonormal θ _ hθ (Work.CharCore.principalChar_mem_Irr (G := ↥N))]
      rw [if_neg hθne]
    have hzero : Work.CharCore.cfInner θ (Work.CharCore.resFun N χ) = 0 := by
      rw [hres, Work.CharCore.cfInner_smul_right, horth, mul_zero]
    exact hc hzero
  have hnt₁' := hnt hθ₁Irr hθ₁ne hc₁
  have hnt₂' := hnt hθ₂Irr hθ₂ne hc₂
  have hmem₁ : χ₁ ∈ Work.FeitSibley.scriptS h.H h.Q1 := by
    simp only [Work.FeitSibley.scriptS, Submission.Blueprint.excludingKernel, Finset.mem_filter]
    exact ⟨hχ₁Irr, hnt₁'⟩
  have hmem₂ : χ₂ ∈ Work.FeitSibley.scriptS h.H h.Q1 := by
    simp only [Work.FeitSibley.scriptS, Submission.Blueprint.excludingKernel, Finset.mem_filter]
    exact ⟨hχ₂Irr, hnt₂'⟩
  -- conclude
  have hsub : ({χ₁, χ₂} : Finset (↥h.H → ℂ)) ⊆ Work.FeitSibley.scriptS h.H h.Q1 := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h
    · rw [h]; exact hmem₁
    · rw [h]; exact hmem₂
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_pair hχne] at hcard
  exact hcard

end Work.FeitSibley.CharQ
