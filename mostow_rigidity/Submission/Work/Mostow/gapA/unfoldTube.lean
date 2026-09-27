import Mathlib
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.bieberbach
import Submission.Work.Mostow.conj_fundamentalDomain
import Submission.Work.Mostow.volH_le_card_mul_of_ae_count

/-!
# `Work.Mostow.gapA.unfoldTube`

If `D` is a fundamental domain of a lattice `Γ` and `Dc` one of the centraliser `C` of `b₀` in `Γ`,
then the set `Tb b₀ η₁ ∩ Dc` of points of `Dc` at which `b₀` is `η₁`-near-identity has measure at
most twice the covolume `volH D` of `Γ`.

The hypothesis `hconj` says that two conjugates of `b₀` which are both near-identity at the *same*
point must be `b₀` or `b₀⁻¹` (this is the ConjCount pigeonhole of `conjCount3`).  The counting
argument shows that every `Γ`-orbit meets `Tb b₀ η₁ ∩ Dc` in at most two points, so unfolding the
measure of `Tb b₀ η₁ ∩ Dc` over the fundamental domain `D` gives the factor `2`.

Main steps:
* `nearIdAt_conj3` : `NearIdAt` is equivariant under conjugation of the isometry;
* `conj_mem_normalizer` : `hconj` shows that only the coset of the "extended normaliser" of `b₀` can
  occur among the elements bringing a near-identity point to another one;
* `count_le_two` : at most two elements of `Γ` bring a good point `z` into `Tb b₀ η₁ ∩ E`;
* `badSet_null` : the "bad" points of `Dc` — those with a non-trivial `C`-translate still in `Dc` —
  are null, even after taking all `Γ`-translates.
-/

set_option maxHeartbeats 1000000

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

/-! ## 1. Equivariance of `NearIdAt` -/

/-- `NearIdAt` is equivariant under conjugation of the isometry and translation of the base point. -/
theorem nearIdAt_conj3 (hA : POActionProp 3) (hI : HypIsometryProp 3) (g h : PO 3 1) (z : E 3)
    (η : ℝ) : NearIdAt g (h • z) η ↔ NearIdAt (h⁻¹ * g * h) z η := by
  have hone : ∀ u : E 3, (1 : PO 3 1) • u = u := hA.2.2.2.1
  have hmul : ∀ (a b : PO 3 1) (u : E 3), (a * b) • u = a • (b • u) := hA.2.2.2.2.1
  have hiso : ∀ (a : PO 3 1) (u v : E 3), hdist (a • u) (a • v) = hdist u v := hI.2.2.2.2.2.2.1
  have hkey : ∀ v : E 3, h • ((h⁻¹ * g * h) • v) = g • (h • v) := by
    intro v
    calc h • ((h⁻¹ * g * h) • v) = (h * (h⁻¹ * g * h)) • v := (hmul h (h⁻¹ * g * h) v).symm
      _ = (g * h) • v := by rw [show h * (h⁻¹ * g * h) = g * h from by group]
      _ = g • (h • v) := hmul g h v
  have hkey2 : ∀ u : E 3, (h⁻¹ * g * h) • (h⁻¹ • u) = h⁻¹ • (g • u) := by
    intro u
    calc (h⁻¹ * g * h) • (h⁻¹ • u) = ((h⁻¹ * g * h) * h⁻¹) • u := (hmul (h⁻¹ * g * h) h⁻¹ u).symm
      _ = (h⁻¹ * g) • u := by rw [show (h⁻¹ * g * h) * h⁻¹ = h⁻¹ * g from by group]
      _ = h⁻¹ • (g • u) := hmul h⁻¹ g u
  constructor
  · intro hg v hv
    have h1 : hdist (h • z) (h • v) ≤ 1 := by rw [hiso h z v]; exact hv
    have h2 : hdist (h • v) (g • (h • v)) < η := hg (h • v) h1
    calc hdist v ((h⁻¹ * g * h) • v)
        = hdist (h • v) (h • ((h⁻¹ * g * h) • v)) := (hiso h v ((h⁻¹ * g * h) • v)).symm
      _ = hdist (h • v) (g • (h • v)) := by rw [hkey v]
      _ < η := h2
  · intro hg u hu
    have h1 : hdist z (h⁻¹ • u) ≤ 1 := by
      calc hdist z (h⁻¹ • u)
          = hdist (h • z) (h • (h⁻¹ • u)) := (hiso h z (h⁻¹ • u)).symm
        _ = hdist (h • z) u := by
            rw [show h • (h⁻¹ • u) = u from by rw [← hmul, mul_inv_cancel, hone]]
        _ ≤ 1 := hu
    have h2 : hdist (h⁻¹ • u) ((h⁻¹ * g * h) • (h⁻¹ • u)) < η := hg (h⁻¹ • u) h1
    calc hdist u (g • u)
        = hdist (h⁻¹ • u) (h⁻¹ • (g • u)) := (hiso h⁻¹ u (g • u)).symm
      _ = hdist (h⁻¹ • u) ((h⁻¹ * g * h) • (h⁻¹ • u)) := by rw [hkey2 u]
      _ < η := h2

/-! ## 2. Measurability of the near-identity set -/

/-- The set of points at which `b` is `η`-near-identity is Borel. -/
theorem measurableSet_Tb (hA : POActionProp 3) (hI : HypIsometryProp 3) (b : PO 3 1) (η : ℝ) :
    MeasurableSet (Tb b η) := by
  have hdist_cont : Continuous (fun p : E 3 × E 3 => hdist p.1 p.2) := hI.2.2.2.2.1
  have hsmul_b : Continuous (fun u : E 3 => b • u) := (hI.2.2.2.2.2.2.2.2.1 b).continuous
  have hcompact : ∀ (u : E 3) (r : ℝ), IsCompact {v : E 3 | hdist u v ≤ r} := hI.2.2.2.2.2.1
  set S : Set (E 3) := {u : E 3 | hdist u (b • u) < η} with hS
  have hScont : Continuous fun u : E 3 => hdist u (b • u) := by
    change Continuous ((fun p : E 3 × E 3 => hdist p.1 p.2) ∘ (fun u : E 3 => (u, b • u)))
    exact hdist_cont.comp (Continuous.prodMk continuous_id hsmul_b)
  have hSopen : IsOpen S := hScont.isOpen_preimage _ isOpen_Iio
  have hSclosed : IsClosed Sᶜ := hSopen.isClosed_compl
  have hAcl : ∀ n : ℕ,
      IsClosed {w : E 3 | ∀ u : ↥Sᶜ, (1 + 1 / ((n : ℝ) + 1)) ≤ hdist w (u : E 3)} := by
    intro n
    have heq : {w : E 3 | ∀ u : ↥Sᶜ, (1 + 1 / ((n : ℝ) + 1)) ≤ hdist w (u : E 3)}
        = ⋂ u : ↥Sᶜ, {w : E 3 | (1 + 1 / ((n : ℝ) + 1)) ≤ hdist w (u : E 3)} := by
      ext w; simp
    rw [heq]
    refine isClosed_iInter fun u => ?_
    have hcont_u : Continuous (fun w : E 3 => hdist w (u : E 3)) := by
      change Continuous ((fun p : E 3 × E 3 => hdist p.1 p.2) ∘ (fun w : E 3 => (w, (u : E 3))))
      exact hdist_cont.comp (Continuous.prodMk continuous_id continuous_const)
    exact isClosed_le continuous_const hcont_u
  have hsub : Tb b η ⊆
      ⋃ n : ℕ, {w : E 3 | ∀ u : ↥Sᶜ, (1 + 1 / ((n : ℝ) + 1)) ≤ hdist w (u : E 3)} := by
    intro w hw
    rw [Set.mem_iUnion]
    by_cases hne : (Sᶜ : Set (E 3)).Nonempty
    · obtain ⟨u₀, hu₀⟩ := hne
      have hKc : IsCompact ({v : E 3 | hdist w v ≤ hdist w u₀ + 1} ∩ Sᶜ) :=
        (hcompact w (hdist w u₀ + 1)).inter_right hSclosed
      have hKne : ({v : E 3 | hdist w v ≤ hdist w u₀ + 1} ∩ Sᶜ).Nonempty :=
        ⟨u₀, by simp [hu₀]⟩
      have hcont_w : Continuous (fun v : E 3 => hdist w v) := by
        change Continuous ((fun p : E 3 × E 3 => hdist p.1 p.2) ∘ (fun v : E 3 => (w, v)))
        exact hdist_cont.comp (Continuous.prodMk continuous_const continuous_id)
      obtain ⟨u₁, hu₁, hmin⟩ := hKc.exists_isMinOn hKne hcont_w.continuousOn
      have hgt : 1 < hdist w u₁ := by
        by_contra hle
        exact hu₁.2 (hw u₁ (not_lt.mp hle))
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hgt)
      refine ⟨n, ?_⟩
      intro u
      have hcase : ∀ v : ↥Sᶜ, hdist w u₁ ≤ hdist w (v : E 3) := by
        intro v
        by_cases hv : hdist w (v : E 3) ≤ hdist w u₀ + 1
        · exact hmin ⟨hv, v.2⟩
        · push_neg at hv
          have h2 := hmin ⟨show hdist w u₀ ≤ hdist w u₀ + 1 from
            le_add_of_nonneg_right zero_le_one, hu₀⟩
          exact le_trans h2 (le_of_lt (lt_trans (lt_add_one _) hv))
      have h3 := hcase u
      have h4 : 1 + 1 / ((n : ℝ) + 1) < hdist w u₁ := by
        simpa [add_comm] using (lt_sub_iff_add_lt.mp hn)
      exact le_trans (le_of_lt h4) h3
    · exact ⟨0, fun u => absurd ⟨u, u.2⟩ hne⟩
  have hsup : (⋃ n : ℕ, {w : E 3 | ∀ u : ↥Sᶜ, (1 + 1 / ((n : ℝ) + 1)) ≤ hdist w (u : E 3)})
      ⊆ Tb b η := by
    intro w hw u hu
    rw [Set.mem_iUnion] at hw
    obtain ⟨n, hn⟩ := hw
    by_contra hcon
    have h1 : (1 : ℝ) + 1 / ((n : ℝ) + 1) ≤ hdist w u := hn ⟨u, hcon⟩
    have h2 : (1 : ℝ) < 1 + 1 / ((n : ℝ) + 1) := by
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    exact (not_lt_of_ge hu) (lt_of_lt_of_le h2 h1)
  rw [show Tb b η
      = ⋃ n : ℕ, {w : E 3 | ∀ u : ↥Sᶜ, (1 + 1 / ((n : ℝ) + 1)) ≤ hdist w (u : E 3)}
      from le_antisymm hsub hsup]
  exact MeasurableSet.iUnion fun n => (hAcl n).measurableSet

/-! ## 3. The ConjCount step -/

/-- If `γ₁ • z` and `γ₂ • z` are both `η₁`-near-identity points of `b₀`, then `γ₂ * γ₁⁻¹`
conjugates `b₀` into `{b₀, b₀⁻¹}`. -/
theorem conj_mem_normalizer (hA : POActionProp 3) (hI : HypIsometryProp 3)
    (Γ : Subgroup (PO 3 1)) (b₀ : PO 3 1) (η₁ : ℝ)
    (hconj : ∀ (w : E 3) (γ : PO 3 1), γ ∈ Γ → NearIdAt b₀ w η₁ →
      NearIdAt (γ⁻¹ * b₀ * γ) w η₁ → γ⁻¹ * b₀ * γ = b₀ ∨ γ⁻¹ * b₀ * γ = b₀⁻¹)
    (z : E 3) (γ₁ γ₂ : ↥Γ)
    (h₁ : NearIdAt b₀ ((γ₁ : PO 3 1) • z) η₁)
    (h₂ : NearIdAt b₀ ((γ₂ : PO 3 1) • z) η₁) :
    (((γ₂ * γ₁⁻¹ : ↥Γ) : PO 3 1))⁻¹ * b₀ * ((γ₂ * γ₁⁻¹ : ↥Γ) : PO 3 1) = b₀ ∨
      (((γ₂ * γ₁⁻¹ : ↥Γ) : PO 3 1))⁻¹ * b₀ * ((γ₂ * γ₁⁻¹ : ↥Γ) : PO 3 1) = b₀⁻¹ := by
  set h : PO 3 1 := ((γ₂ * γ₁⁻¹ : ↥Γ) : PO 3 1) with hh
  have hmem : h ∈ Γ := (γ₂ * γ₁⁻¹ : ↥Γ).2
  have hnear : NearIdAt (h⁻¹ * b₀ * h) ((γ₁ : PO 3 1) • z) η₁ := by
    rw [nearIdAt_conj3 hA hI (h⁻¹ * b₀ * h) (γ₁ : PO 3 1) z η₁]
    have heq : (γ₁ : PO 3 1)⁻¹ * (h⁻¹ * b₀ * h) * (γ₁ : PO 3 1)
        = (γ₂ : PO 3 1)⁻¹ * b₀ * (γ₂ : PO 3 1) := by
      rw [hh, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [heq]
    exact (nearIdAt_conj3 hA hI b₀ (γ₂ : PO 3 1) z η₁).mp h₂
  exact hconj ((γ₁ : PO 3 1) • z) h hmem h₁ hnear

/-! ## 4. The counting bound -/

/-- **Counting bound.** If every `Γ`-translate of `z` that lies in `E` is "good" (`E` contains no
two points of a single non-trivial `C`-orbit, `C` the centraliser of `b₀` in `Γ`), then at most two
elements `γ : Γ` have `γ • z ∈ Tb b₀ η₁ ∩ E`. -/
theorem count_le_two (hA : POActionProp 3) (hI : HypIsometryProp 3)
    (Γ : Subgroup (PO 3 1)) (b₀ : PO 3 1) (η₁ : ℝ)
    (hconj : ∀ (w : E 3) (γ : PO 3 1), γ ∈ Γ → NearIdAt b₀ w η₁ →
      NearIdAt (γ⁻¹ * b₀ * γ) w η₁ → γ⁻¹ * b₀ * γ = b₀ ∨ γ⁻¹ * b₀ * γ = b₀⁻¹)
    (Es : Set (E 3)) (z : E 3)
    (hgood : ∀ (γ : Γ) (c : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ)), c ≠ 1 →
      (γ : PO 3 1) • z ∈ Es → (c : PO 3 1) • ((γ : PO 3 1) • z) ∉ Es) :
    ∃ s : Finset Γ, s.card ≤ 2 ∧
      ∀ γ : Γ, (γ : PO 3 1) • z ∈ Tb b₀ η₁ ∩ Es → γ ∈ s := by
  classical
  have hone : ∀ u : E 3, (1 : PO 3 1) • u = u := hA.2.2.2.1
  have hmul : ∀ (a b : PO 3 1) (u : E 3), (a * b) • u = a • (b • u) := hA.2.2.2.2.1
  by_cases hS : ∃ γ : Γ, (γ : PO 3 1) • z ∈ Tb b₀ η₁ ∩ Es
  · obtain ⟨γ₁, hγ₁⟩ := hS
    have hz₁T : NearIdAt b₀ ((γ₁ : PO 3 1) • z) η₁ := hγ₁.1
    have hz₁E : (γ₁ : PO 3 1) • z ∈ Es := hγ₁.2
    -- the ConjCount step: `γ * γ₁⁻¹` conjugates `b₀` to `b₀` or `b₀⁻¹`
    have hNmem : ∀ γ : Γ, (γ : PO 3 1) • z ∈ Tb b₀ η₁ →
        (((γ * γ₁⁻¹ : ↥Γ) : PO 3 1))⁻¹ * b₀ * ((γ * γ₁⁻¹ : ↥Γ) : PO 3 1) = b₀ ∨
        (((γ * γ₁⁻¹ : ↥Γ) : PO 3 1))⁻¹ * b₀ * ((γ * γ₁⁻¹ : ↥Γ) : PO 3 1) = b₀⁻¹ :=
      fun γ hγ => conj_mem_normalizer hA hI Γ b₀ η₁ hconj z γ₁ γ hz₁T hγ
    -- two "twisted" elements with a translate in `E` coincide
    have hsub : ∀ h h' : Γ, ((h : PO 3 1))⁻¹ * b₀ * (h : PO 3 1) = b₀⁻¹ →
        (h : PO 3 1) • ((γ₁ : PO 3 1) • z) ∈ Es →
        ((h' : PO 3 1))⁻¹ * b₀ * (h' : PO 3 1) = b₀⁻¹ →
        (h' : PO 3 1) • ((γ₁ : PO 3 1) • z) ∈ Es → h = h' := by
      intro h h' eh ehE eh' eh'E
      by_contra hne
      have key : ∀ x y : PO 3 1, x⁻¹ * b₀ * x = b₀⁻¹ → y⁻¹ * b₀ * y = b₀⁻¹ →
          (x * y⁻¹) * b₀ * (x * y⁻¹)⁻¹ = b₀ := by
        intro x y ex ey
        have hx : x * b₀⁻¹ * x⁻¹ = b₀ := by rw [← ex]; group
        calc (x * y⁻¹) * b₀ * (x * y⁻¹)⁻¹ = x * (y⁻¹ * b₀ * y) * x⁻¹ := by group
          _ = x * b₀⁻¹ * x⁻¹ := by rw [ey]
          _ = b₀ := hx
      have hc : ((h * h'⁻¹ : ↥Γ) : PO 3 1) * b₀ * (((h * h'⁻¹ : ↥Γ) : PO 3 1))⁻¹ = b₀ := by
        have hkey := key (h : PO 3 1) (h' : PO 3 1) eh eh'
        simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hkey
      have hcent : ((h * h'⁻¹ : ↥Γ) : PO 3 1) ∈ Subgroup.centralizer ({b₀} : Set (PO 3 1)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        conv_lhs => rw [← hc]
        group
      have hΓmem : ((h * h'⁻¹ : ↥Γ) : PO 3 1) ∈ Γ := (h * h'⁻¹ : ↥Γ).2
      set c : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) :=
        ⟨((h * h'⁻¹ : ↥Γ) : PO 3 1), hcent, hΓmem⟩ with hcdef
      have hcne : c ≠ 1 := by
        intro hcon
        apply hne
        have h2 := congrArg
          (fun x : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) => (x : PO 3 1)) hcon
        have h1 : (h * h'⁻¹ : ↥Γ) = 1 := by
          apply Subtype.ext
          simpa [hcdef] using h2
        exact mul_inv_eq_one.mp h1
      have hmemE : ((h' * γ₁ : ↥Γ) : PO 3 1) • z ∈ Es := by
        have he : ((h' * γ₁ : ↥Γ) : PO 3 1) • z = (h' : PO 3 1) • ((γ₁ : PO 3 1) • z) := by
          rw [Subgroup.coe_mul, hmul]
        rw [he]; exact eh'E
      have hcontra := hgood (h' * γ₁) c hcne hmemE
      apply hcontra
      have he : (c : PO 3 1) • (((h' * γ₁ : ↥Γ) : PO 3 1) • z)
          = (h : PO 3 1) • ((γ₁ : PO 3 1) • z) := by
        rw [← hmul, ← hmul]
        congr 1
        show ((h * h'⁻¹ : ↥Γ) : PO 3 1) * ((h' * γ₁ : ↥Γ) : PO 3 1)
            = (h : PO 3 1) * (γ₁ : PO 3 1)
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [he]; exact ehE
    have hz₁E' : ∀ h : Γ, ((h * γ₁ : ↥Γ) : PO 3 1) • z = (h : PO 3 1) • ((γ₁ : PO 3 1) • z) :=
      fun h => by rw [Subgroup.coe_mul, hmul]
    have hcomm_conv : ∀ h : Γ, ((h : PO 3 1))⁻¹ * b₀ * (h : PO 3 1) = b₀ →
        b₀ * (h : PO 3 1) = (h : PO 3 1) * b₀ := by
      intro h hh
      have := congrArg (fun x => (h : PO 3 1) * x) hh
      simpa [mul_assoc] using this
    -- the case where `γ * γ₁⁻¹` centralises `b₀`
    have htriv : ∀ γ : Γ, (γ : PO 3 1) • z ∈ Tb b₀ η₁ ∩ Es →
        (((γ * γ₁⁻¹ : ↥Γ) : PO 3 1))⁻¹ * b₀ * ((γ * γ₁⁻¹ : ↥Γ) : PO 3 1) = b₀ →
        γ = γ₁ := by
      intro γ hγ hcomm
      set h : Γ := γ * γ₁⁻¹ with hhdef
      have hcomm' : ((h : PO 3 1))⁻¹ * b₀ * (h : PO 3 1) = b₀ := by simpa [hhdef] using hcomm
      have hzE : (h : PO 3 1) • ((γ₁ : PO 3 1) • z) ∈ Es := by
        rw [← hz₁E' h]
        have heq : ((h * γ₁ : ↥Γ)) = (γ : ↥Γ) := by
          rw [hhdef]; group
        rw [heq]
        exact hγ.2
      have h1 : h = 1 := by
        by_contra hne
        have hcent : (h : PO 3 1) ∈ Subgroup.centralizer ({b₀} : Set (PO 3 1)) := by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact hcomm_conv h hcomm'
        have hcne : (⟨(h : PO 3 1), hcent, h.2⟩ :
            ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ)) ≠ 1 := by
          intro hcon
          apply hne
          apply Subtype.ext
          have h2 := congrArg
            (fun x : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) => (x : PO 3 1)) hcon
          simpa using h2
        exact (hgood γ₁ ⟨(h : PO 3 1), hcent, h.2⟩ hcne hz₁E) hzE
      have h2 : (γ * γ₁⁻¹ : ↥Γ) = 1 := by rw [← hhdef]; exact h1
      exact mul_inv_eq_one.mp h2
    by_cases hB : ∃ h : Γ, ((h : PO 3 1))⁻¹ * b₀ * (h : PO 3 1) = b₀⁻¹ ∧
        (h : PO 3 1) • ((γ₁ : PO 3 1) • z) ∈ Es
    · obtain ⟨h₀, hh₀₁, hh₀₂⟩ := hB
      refine ⟨{γ₁, h₀ * γ₁}, ?_, ?_⟩
      · have hcard := Finset.card_insert_le γ₁ ({h₀ * γ₁} : Finset Γ)
        simpa using hcard
      · intro γ hγ
        rcases hNmem γ hγ.1 with hcomm | hcomm
        · have hmem : γ₁ ∈ ({γ₁, h₀ * γ₁} : Finset Γ) := Finset.mem_insert_self γ₁ _
          rw [htriv γ hγ hcomm]
          exact hmem
        · have hzE : (γ * γ₁⁻¹ : ↥Γ) • ((γ₁ : PO 3 1) • z) ∈ Es := by
            show (((γ * γ₁⁻¹ : ↥Γ)) : PO 3 1) • ((γ₁ : PO 3 1) • z) ∈ Es
            rw [← hz₁E' (γ * γ₁⁻¹)]
            have heq : (((γ * γ₁⁻¹) * γ₁ : ↥Γ)) = (γ : ↥Γ) := by group
            rw [heq]
            exact hγ.2
          have hh : (γ * γ₁⁻¹ : ↥Γ) = h₀ :=
            hsub (γ * γ₁⁻¹) h₀ hcomm hzE hh₀₁ hh₀₂
          have hγeq : γ = h₀ * γ₁ := by
            rw [← hh]
            group
          have hmem : h₀ * γ₁ ∈ ({γ₁, h₀ * γ₁} : Finset Γ) :=
            Finset.mem_insert_of_mem (Finset.mem_singleton_self (h₀ * γ₁))
          rw [hγeq]
          exact hmem
    · refine ⟨{γ₁}, ?_, ?_⟩
      · simp
      · intro γ hγ
        rw [Finset.mem_singleton]
        rcases hNmem γ hγ.1 with hcomm | hcomm
        · exact htriv γ hγ hcomm
        · refine absurd ?_ hB
          refine ⟨γ * γ₁⁻¹, hcomm, ?_⟩
          show (((γ * γ₁⁻¹ : ↥Γ)) : PO 3 1) • ((γ₁ : PO 3 1) • z) ∈ Es
          rw [← hz₁E' (γ * γ₁⁻¹)]
          have heq : (((γ * γ₁⁻¹) * γ₁ : ↥Γ)) = (γ : ↥Γ) := by group
          rw [heq]
          exact hγ.2
  · exact ⟨∅, by simp, fun γ hγ => absurd ⟨γ, hγ⟩ hS⟩

/-! ## 5. The `C`-bad points of `Dc` are null -/

/-- Points of `Dc` with a non-trivial centraliser translate still inside `Dc` are null, even after
taking all their `Γ`-translates. -/
theorem badSet_null (hA : POActionProp 3) (hI : HypIsometryProp 3)
    (Γ : Subgroup (PO 3 1)) (hdisc : IsDiscrete (SetLike.coe Γ))
    (b₀ : PO 3 1) (Dc : Set (E 3))
    (hDc : IsFundamentalDomain
      ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) Dc (volH 3)) :
    volH 3 (⋃ γ : Γ, (fun x => (γ : PO 3 1) • x) ''
      {x : E 3 | x ∈ Dc ∧ ∃ c : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ),
        c ≠ 1 ∧ (c : PO 3 1) • x ∈ Dc}) = 0 := by
  have hone : ∀ u : E 3, (1 : PO 3 1) • u = u := hA.2.2.2.1
  have hmul : ∀ (a b : PO 3 1) (u : E 3), (a * b) • u = a • (b • u) := hA.2.2.2.2.1
  letI : MulAction (PO 3 1) (E 3) := { one_smul := hone, mul_smul := hmul }
  have hmp : ∀ g : PO 3 1, MeasurePreserving (fun u : E 3 => g • u) (volH 3) (volH 3) :=
    fun g => hI.2.2.2.2.2.2.2.2.2.2.2.1 g
  haveI : SMulInvariantMeasure (PO 3 1) (E 3) (volH 3) :=
    ⟨fun c s hs => (hmp c).measure_preimage hs.nullMeasurableSet⟩
  letI : MulAction ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) (E 3) := inferInstance
  letI : MulAction Γ (E 3) := inferInstance
  haveI : SMulInvariantMeasure ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) (E 3) (volH 3) :=
    ⟨fun c s hs => (hmp (c : PO 3 1)).measure_preimage hs.nullMeasurableSet⟩
  haveI : SMulInvariantMeasure Γ (E 3) (volH 3) :=
    ⟨fun c s hs => (hmp (c : PO 3 1)).measure_preimage hs.nullMeasurableSet⟩
  haveI : Countable Γ := countable_of_isDiscrete (PO 3 1) hdisc
  haveI : Countable ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) := by
    have hf : Function.Injective
        (fun c : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) =>
          (⟨(c : PO 3 1), c.2.2⟩ : Γ)) := by
      intro a b hab
      exact Subtype.ext (by simpa using congrArg (fun x : Γ => (x : PO 3 1)) hab)
    exact hf.countable
  -- a single non-trivial pair of translates is null
  have hpair : ∀ c : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ), c ≠ 1 →
      volH 3 ((fun x : E 3 => (c : PO 3 1)⁻¹ • x) '' Dc ∩ Dc) = 0 := by
    intro c hc
    have h1 := hDc.aedisjoint (show (1 : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ)) ≠ c
      from fun h => hc h.symm)
    dsimp only [Function.onFun] at h1
    have h2 : ((1 : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ)) • Dc : Set (E 3)) = Dc := by
      show (fun x : E 3 => (1 : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ)) • x) '' Dc = Dc
      rw [show (fun x : E 3 =>
            (1 : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ)) • x) = fun x : E 3 => x
          from funext fun x => hone x]
      exact Set.image_id Dc
    rw [h2] at h1
    have h3 : volH 3 (Dc ∩ ((c : PO 3 1) • Dc)) = 0 := h1
    have h4 : volH 3 ((c : PO 3 1)⁻¹ • (Dc ∩ (c : PO 3 1) • Dc)) = 0 := by
      rw [measure_smul]
      exact h3
    have h5 : (c : PO 3 1)⁻¹ • (Dc ∩ (c : PO 3 1) • Dc)
        = ((c : PO 3 1)⁻¹ • Dc) ∩ Dc := by
      rw [Set.smul_set_inter]
      congr 1
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨z, hz, hzy⟩ := Set.mem_smul_set.mp hy
        show (c : PO 3 1)⁻¹ • y ∈ Dc
        rw [← hzy, ← hmul, inv_mul_cancel, hone]
        exact hz
      · intro hx
        refine ⟨(c : PO 3 1) • x, ⟨x, hx, rfl⟩, ?_⟩
        show (c : PO 3 1)⁻¹ • ((c : PO 3 1) • x) = x
        rw [← hmul, inv_mul_cancel, hone]
    rw [h5] at h4
    exact h4
  -- the bad set is null
  have hbad : volH 3 {x : E 3 | x ∈ Dc ∧ ∃ c : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ),
      c ≠ 1 ∧ (c : PO 3 1) • x ∈ Dc} = 0 := by
    refine measure_mono_null ?_ (measure_iUnion_null fun c : {c : ↥(Subgroup.centralizer
        ({b₀} : Set (PO 3 1)) ⊓ Γ) // c ≠ 1} => hpair c c.2)
    intro x hx
    obtain ⟨hxD, c, hc, hcx⟩ := hx
    refine Set.mem_iUnion.mpr ⟨⟨c, hc⟩, ⟨?_, hxD⟩⟩
    show x ∈ (c : PO 3 1)⁻¹ • Dc
    exact Set.mem_smul_set.mpr ⟨(c : PO 3 1) • x, hcx, by
      show (c : PO 3 1)⁻¹ • ((c : PO 3 1) • x) = x
      rw [← hmul, inv_mul_cancel, hone]⟩
  -- the union of all `Γ`-translates is null
  refine measure_iUnion_null fun γ : Γ => ?_
  show volH 3 ((γ : PO 3 1) • {x : E 3 | x ∈ Dc ∧ ∃ c : ↥(Subgroup.centralizer
      ({b₀} : Set (PO 3 1)) ⊓ Γ), c ≠ 1 ∧ (c : PO 3 1) • x ∈ Dc}) = 0
  rw [measure_smul]
  exact hbad

/-! ## 6. The main theorem -/

theorem unfoldTube (hA : Submission.Mostow.POActionProp 3) (hI : Submission.Mostow.HypIsometryProp 3)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO 3 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (b₀ : LeanEval.Geometry.MostowRigidity.PO 3 1) (η₁ : ℝ)
    (hconj : ∀ (w : Submission.Mostow.E 3) (γ : LeanEval.Geometry.MostowRigidity.PO 3 1),
      γ ∈ Γ → Submission.Mostow.NearIdAt b₀ w η₁ → Submission.Mostow.NearIdAt (γ⁻¹ * b₀ * γ) w η₁ →
      γ⁻¹ * b₀ * γ = b₀ ∨ γ⁻¹ * b₀ * γ = b₀⁻¹)
    (D Dc : Set (Submission.Mostow.E 3)) (hD : MeasureTheory.IsFundamentalDomain ↥Γ D (Submission.Mostow.volH 3))
    (hDc : MeasureTheory.IsFundamentalDomain
      ↥(Subgroup.centralizer ({b₀} : Set (LeanEval.Geometry.MostowRigidity.PO 3 1)) ⊓ Γ) Dc
      (Submission.Mostow.volH 3)) :
    Submission.Mostow.volH 3 (Work.Mostow.Tb b₀ η₁ ∩ Dc) ≤ 2 * Submission.Mostow.volH 3 D := by
  obtain ⟨hdisc, -⟩ := hΓ
  have hone : ∀ u : E 3, (1 : PO 3 1) • u = u := hA.2.2.2.1
  have hmul : ∀ (a b : PO 3 1) (u : E 3), (a * b) • u = a • (b • u) := hA.2.2.2.2.1
  letI : MulAction (PO 3 1) (E 3) := { one_smul := hone, mul_smul := hmul }
  letI : MulAction Γ (E 3) := inferInstance
  have hId : HypIsoData 3 := HypIsoData.ofProp hI
  have hmp : ∀ g : PO 3 1, MeasurePreserving (fun u : E 3 => g • u) (volH 3) (volH 3) :=
    fun g => hId.measurePreserving_smul g
  haveI : SMulInvariantMeasure (PO 3 1) (E 3) (volH 3) :=
    ⟨fun c s hs => (hmp c).measure_preimage hs.nullMeasurableSet⟩
  haveI : MeasurableConstSMul Γ (E 3) :=
    ⟨fun c => (hId.contDiff_smul (c : PO 3 1)).continuous.measurable⟩
  haveI : SMulInvariantMeasure Γ (E 3) (volH 3) :=
    ⟨fun c s hs => (hId.measurePreserving_smul (c : PO 3 1)).measure_preimage hs.nullMeasurableSet⟩
  haveI : Countable Γ := countable_of_isDiscrete (PO 3 1) hdisc
  haveI : Countable ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) := by
    have hf : Function.Injective
        (fun c : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ) =>
          (⟨(c : PO 3 1), c.2.2⟩ : Γ)) := by
      intro a b hab
      exact Subtype.ext (by simpa using congrArg (fun x : Γ => (x : PO 3 1)) hab)
    exact hf.countable
  -- replace `Dc` by a measurable hull
  set DcM : Set (E 3) := toMeasurable (volH 3) Dc with hDcM
  have hDcM_meas : MeasurableSet DcM := measurableSet_toMeasurable _ _
  have hDcM_ae : DcM =ᵐ[volH 3] Dc := hDc.nullMeasurableSet.toMeasurable_ae_eq
  have hdiff : volH 3 (DcM \ Dc) = 0 := (ae_eq_set.mp hDcM_ae).1
  set BadM : Set (E 3) := {x : E 3 | x ∈ DcM ∧
    ∃ c : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ), c ≠ 1 ∧ (c : PO 3 1) • x ∈ DcM}
    with hBadM
  have hBadM_null : volH 3 BadM = 0 := by
    have hzero : volH 3 ((DcM \ Dc) ∪
        ({x : E 3 | x ∈ Dc ∧ ∃ c : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ),
            c ≠ 1 ∧ (c : PO 3 1) • x ∈ Dc}
          ∪ ⋃ c : ↥(Subgroup.centralizer ({b₀} : Set (PO 3 1)) ⊓ Γ),
              (fun x : E 3 => (c : PO 3 1)⁻¹ • x) '' (DcM \ Dc))) = 0 := by
      refine measure_union_null hdiff (measure_union_null ?_ ?_)
      · -- the bad set of `Dc` is null
        refine measure_mono_null ?_ (badSet_null hA hI Γ hdisc b₀ Dc hDc)
        intro x hx
        exact Set.mem_iUnion.mpr ⟨1, ⟨x, hx, hone x⟩⟩
      · refine measure_iUnion_null fun c => ?_
        show volH 3 ((c : PO 3 1)⁻¹ • (DcM \ Dc)) = 0
        rw [measure_smul]
        exact hdiff
    refine measure_mono_null ?_ hzero
    intro x hx
    obtain ⟨hxDcM, c, hc, hcx⟩ := hx
    by_cases hxDc : x ∈ Dc
    · by_cases hcxDc : (c : PO 3 1) • x ∈ Dc
      · exact Set.mem_union_right _ (Set.mem_union_left _ ⟨hxDc, c, hc, hcxDc⟩)
      · refine Set.mem_union_right _ (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨c, ?_⟩))
        exact Set.mem_smul_set.mpr ⟨(c : PO 3 1) • x, ⟨hcx, hcxDc⟩, by
          show (c : PO 3 1)⁻¹ • ((c : PO 3 1) • x) = x
          rw [← hmul, inv_mul_cancel, hone]⟩
    · exact Set.mem_union_left _ ⟨hxDcM, hxDc⟩
  have hBadAll_null : volH 3 (⋃ γ : Γ, (γ : PO 3 1) • BadM) = 0 := by
    refine measure_iUnion_null fun γ : Γ => ?_
    rw [measure_smul]
    exact hBadM_null
  -- the counting hypothesis
  have hcount : ∀ᵐ z ∂((volH 3).restrict D), ∃ s : Finset Γ, s.card ≤ 2 ∧
      ∀ γ : Γ, (γ : PO 3 1) • z ∈ Tb b₀ η₁ ∩ DcM → γ ∈ s := by
    rw [MeasureTheory.ae_restrict_iff'₀ hD.nullMeasurableSet]
    filter_upwards [(measure_eq_zero_iff_ae_notMem.mp hBadAll_null)] with z hz hzD
    refine count_le_two hA hI Γ b₀ η₁ hconj DcM z ?_
    intro γ c hc hγE hcx
    have hmem : (γ : PO 3 1) • z ∈ BadM := ⟨hγE, c, hc, hcx⟩
    have hmem2 : z ∈ ⋃ γ' : Γ, (γ' : PO 3 1) • BadM :=
      Set.mem_iUnion.mpr ⟨γ⁻¹, Set.mem_smul_set.mpr ⟨(γ : PO 3 1) • z, hmem,
        by rw [← hmul, Subgroup.coe_inv, inv_mul_cancel, hone]⟩⟩
    exact hz hmem2
  -- assemble
  have hFmeas : MeasurableSet (Tb b₀ η₁ ∩ DcM) :=
    (measurableSet_Tb hA hI b₀ η₁).inter hDcM_meas
  have hvol_eq : volH 3 (Tb b₀ η₁ ∩ Dc) = volH 3 (Tb b₀ η₁ ∩ DcM) :=
    measure_congr (ae_eq_set_inter (ae_eq_refl _) hDcM_ae.symm)
  have hmain := volH_le_card_mul_of_ae_count 3 hA hI Γ hdisc hD hFmeas 2 hcount
  rw [hvol_eq]
  exact hmain

end

end Work.Mostow.gapA
