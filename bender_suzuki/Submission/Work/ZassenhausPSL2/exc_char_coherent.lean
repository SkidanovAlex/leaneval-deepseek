import Submission.Work.ZassenhausPSL2.ZData.ExcCharSetup
import Submission.Work.CharCore.classFun_eq_sum_irr
import Submission.Work.Coherence.coherent_of_norm_two_lift
import Submission.Work.FeitSibley.CharQ.isometry_indLin

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The exceptional characters of an abelian T.I.F.N. subgroup are coherent

`Work.ZassenhausPSL2.exc_char_coherent` (Isaacs, *Character Theory of Finite Groups*,
Corollary 7.18(a),(b), i.e. the abelian case of the Feit–Sibley exceptional-character theorem):
if `K` is an abelian T.I.F.N. subgroup of the finite group `W` — a T.I. subgroup with
`C_W(k) ≤ K` for `1 ≠ k ∈ K` — then the set `𝒮 = {χ ∈ Irr N_W(K) | K ⊄ ker χ}` is coherent for
induction `Ind_{N_W(K)}^W`.

The proof follows Feit/Isaacs:

* every `χ ∈ 𝒮` is induced from a non-principal character of `K` (`scriptS_eq_induced`), hence
  has degree `[N_W(K) : K]` (`scriptS_degree`) and vanishes off `K` (`scriptS_vanish`);
* the Dade/Brauer–Suzuki isometry `⟨α^W, β^W⟩ = ⟨α, β⟩` on `ℤ[𝒮]⁰` (`isometryOn_scriptS`), from
  the TI-set form `Work.BrauerSuzuki.TI.cfInner_indFun_eq_of_TISet`;
* `(χ - x₀)^W` is a virtual character of degree zero (`isVChar_indLin_sub`), so
  `Work.Coherence.coherent_of_norm_two_lift` (FT Lemma 10.1 / Isaacs Corollary 7.15) applies as
  soon as `|𝒮| ≥ 2`; the remaining case `|𝒮| ≤ 1` is `coherent_of_card_le_one`.
-/

namespace Work.ZassenhausPSL2

open Classical

noncomputable section

variable {W : Type} [Group W] [Fintype W]

/-! ## Orthonormality of `𝒮` -/

/-- `𝒮` is an orthonormal set: it consists of irreducible characters. -/
lemma orthonormal_scriptS (K : Subgroup W) : Work.Coherence.Orthonormal (scriptS K) :=
  Work.Coherence.Orthonormal.mono Work.CharCore.Orthonormal_Irr (scriptS_subset_Irr K)

/-! ## The structure of `𝒮`: every member is induced from `K` -/

/-- **The inertia group of a non-principal character of `K` in `N_W(K)` is `K`.**

If `g ∈ N_W(K)` fixes `θ ∈ Irr K` (viewed inside `N_W(K)`), then either `g ∈ K` or `θ = 1`:
if `g ∉ K` then conjugation by `g` is a fixed-point-free automorphism of `K` (a fixed `k ≠ 1`
would give `g ∈ C_W(k) ≤ K`), and a fixed-point-free automorphism has no non-trivial invariant
irreducible character (`Work.Frobenius.Induced.conjChar_ne_self_of_fpf`). -/
lemma inertia_eq (K : Subgroup W)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) ≤ K)
    {θ : ↥(Kn K) → ℂ} (hθ : θ ∈ Work.CharCore.Irr ↥(Kn K)) (hθ1 : θ ≠ 1) :
    Work.Clifford.inertia (Kn K) θ = Kn K := by
  have hθCl : θ ∈ Work.Clifford.Irr ↥(Kn K) := (Work.Clifford.mem_Irr_charCore_iff).mpr hθ
  have hθF : θ ∈ Work.Frobenius.Irr ↥(Kn K) :=
    (Work.Frobenius.Bridge.mem_Irr_iff_coherence).mpr
      ((Work.Clifford.mem_Irr_iff_coherence (G := ↥(Kn K))).mp hθCl)
  refine le_antisymm ?_ (Work.Clifford.le_inertia_of_mem_Irr hθCl)
  intro g hg
  rw [Work.Clifford.mem_inertia] at hg
  by_contra hgK
  -- conjugation by `g` is fixed-point-free on `Kn K`
  have hfpf : ∀ k : ↥(nrm K), k ∈ Kn K → g * k * g⁻¹ = k → k = 1 := by
    intro k hk hkeq
    by_contra hk1
    have hkW : (k : W) ∈ K := (Subgroup.mem_subgroupOf).mp hk
    have hkne : (k : W) ≠ 1 := fun h => hk1 (Subtype.ext h)
    have hmem : (g : W) ∈ Subgroup.centralizer ({(k : W)} : Set W) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : (g : W) * (k : W) * (g : W)⁻¹ = (k : W) :=
        congrArg (fun z : ↥(nrm K) => (z : W)) hkeq
      calc (g : W) * (k : W) = ((g : W) * (k : W) * (g : W)⁻¹) * (g : W) := by group
        _ = (k : W) * (g : W) := by rw [h1]
    exact hgK (hcent (k : W) hkW hkne hmem)
  have hne := Work.Frobenius.Induced.conjChar_ne_self_of_fpf
    (G := ↥(nrm K)) (K := Kn K) hθF hθ1 hfpf
  rw [Work.Frobenius.Induced.conjChar_eq_conjFun] at hne
  exact hne hg

/-- **Induction of a non-principal character of the kernel is irreducible.**

For `θ ∈ Irr K` non-principal with `I_{N_W(K)}(θ) = K`, the induced function
`Ind_K^{N_W(K)} θ` is an irreducible character: its norm is `|I(θ)|/|K| = 1`
(`Work.Clifford.cfInner_indFun_normal'`), it is a virtual character
(`Work.Induction.isVChar_indFun`), and `Work.CharCore.vchar_norm_one` plus positivity of the
degree (`Work.Induction.indFun_apply_one`) identifies it. -/
lemma ind_irr (K : Subgroup W)
    {θ : ↥(Kn K) → ℂ} (hθ : θ ∈ Work.CharCore.Irr ↥(Kn K)) (hθ1 : θ ≠ 1)
    (hinertia : Work.Clifford.inertia (Kn K) θ = Kn K) :
    Work.Induction.indFun (Kn K) θ ∈ Work.CharCore.Irr ↥(nrm K) := by
  have hθCl : θ ∈ Work.Clifford.Irr ↥(Kn K) := (Work.Clifford.mem_Irr_charCore_iff).mpr hθ
  have hcard : (Nat.card ↥(Kn K) : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card, Nat.cast_ne_zero]; exact Fintype.card_ne_zero
  have hidx : ((Kn K).index : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Subgroup.index_ne_zero_of_finite (H := Kn K))
  have hnorm : Work.CharCore.cfInner (Work.Induction.indFun (Kn K) θ)
      (Work.Induction.indFun (Kn K) θ) = 1 := by
    rw [Work.Clifford.cfInner_indFun_normal' (N := Kn K) hθCl, hinertia]
    exact mul_inv_cancel₀ hcard
  have hV : Work.CharCore.IsVChar (Work.Induction.indFun (Kn K) θ) :=
    Work.Induction.isVChar_indFun (Work.CharCore.IsVChar.of_mem_Irr hθ)
  obtain ⟨χ, hχIrr, hcase⟩ := Work.CharCore.vchar_norm_one hV hnorm
  rcases hcase with h | h
  · rw [h]; exact hχIrr
  · exfalso
    have h1 : Work.Induction.indFun (Kn K) θ 1 = -χ 1 := by rw [h]; rfl
    rw [Work.Induction.indFun_apply_one, Work.CharCore.irrDeg_spec hθ,
      Work.CharCore.irrDeg_spec hχIrr] at h1
    have h2 : (((Kn K).index : ℝ) * (Work.CharCore.irrDeg θ : ℝ))
        = -((Work.CharCore.irrDeg χ : ℝ)) := by
      apply Complex.ofReal_injective
      push_cast
      exact h1
    have h4 : (0 : ℝ) < ((Kn K).index : ℝ) * (Work.CharCore.irrDeg θ : ℝ) :=
      mul_pos (Nat.cast_pos.mpr
        (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := Kn K))))
        (Work.CharCore.irrDeg_pos' hθ)
    have h5 : (0 : ℝ) < (Work.CharCore.irrDeg χ : ℝ) := Work.CharCore.irrDeg_pos' hχIrr
    linarith

/-- **The structure of `𝒮`.**  Every `χ ∈ 𝒮` is induced from a non-principal irreducible
character of `K`: `χ|_K` has a non-principal constituent `θ` (otherwise it would be constant and
`K` would lie in `ker χ`), its inertia group is `K` (`inertia_eq`), so `Ind_K^{N_W(K)} θ` is an
irreducible character (`ind_irr`) that pairs non-trivially with `χ` (Frobenius reciprocity), hence
equals `χ`. -/
lemma scriptS_eq_induced (K : Subgroup W)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) ≤ K)
    {χ : ↥(nrm K) → ℂ} (hχ : χ ∈ scriptS K) :
    ∃ θ : ↥(Kn K) → ℂ, θ ∈ Work.CharCore.Irr ↥(Kn K) ∧ θ ≠ 1 ∧
      χ = Work.Induction.indFun (Kn K) θ := by
  obtain ⟨hχIrr, x₀, hx₀K, hx₀ne⟩ := (mem_scriptS K).mp hχ
  -- ### Step 1: `χ|_K` has a non-principal constituent
  have hstep1 : ∃ θ ∈ Work.CharCore.Irr ↥(Kn K), θ ≠ 1 ∧
      Work.CharCore.cfInner (Work.Clifford.resFun (Kn K) χ) θ ≠ 0 := by
    by_contra hcon
    have hcon' : ∀ θ ∈ Work.CharCore.Irr ↥(Kn K), θ ≠ 1 →
        Work.CharCore.cfInner (Work.Clifford.resFun (Kn K) χ) θ = 0 := by
      intro θ hθ hθ1
      by_contra hne
      exact hcon ⟨θ, hθ, hθ1, hne⟩
    have hχcf : Work.CharCore.IsClassFun χ := Work.CharCore.isClassFun_of_mem_Irr hχIrr
    have hrescf : Work.CharCore.IsClassFun (Work.Clifford.resFun (Kn K) χ) := by
      intro a b
      exact hχcf a b
    have hsum := Work.CharCore.classFun_eq_sum_irr hrescf
    have hsingle : (∑ y ∈ Work.CharCore.Irr ↥(Kn K),
          (Work.CharCore.cfInner (Work.Clifford.resFun (Kn K) χ) y) • y)
        = (Work.CharCore.cfInner (Work.Clifford.resFun (Kn K) χ) 1) •
            (1 : ↥(Kn K) → ℂ) := by
      refine Finset.sum_eq_single (1 : ↥(Kn K) → ℂ) ?_ ?_
      · intro b hb hb1
        rw [hcon' b hb hb1, zero_smul]
      · intro hnot
        exact absurd (Work.CharCore.principalChar_mem_Irr (G := ↥(Kn K))) hnot
    have hcollapse : Work.Clifford.resFun (Kn K) χ =
        (Work.CharCore.cfInner (Work.Clifford.resFun (Kn K) χ) 1) • (1 : ↥(Kn K) → ℂ) :=
      hsum.trans hsingle
    have hval := congrFun hcollapse (⟨x₀, hx₀K⟩ : ↥(Kn K))
    have hval1 := congrFun hcollapse (1 : ↥(Kn K))
    simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] at hval hval1
    exact hx₀ne (hval.trans hval1.symm)
  -- ### Step 2: `χ = Ind_K^{N_W(K)} θ`
  obtain ⟨θ, hθIrr, hθ1, hpair⟩ := hstep1
  have hIndIrr : Work.Induction.indFun (Kn K) θ ∈ Work.CharCore.Irr ↥(nrm K) :=
    ind_irr K hθIrr hθ1 (inertia_eq K hcent hθIrr hθ1)
  refine ⟨θ, hθIrr, hθ1, ?_⟩
  have hpair' : Work.CharCore.cfInner χ (Work.Induction.indFun (Kn K) θ) ≠ 0 := by
    intro hzero
    -- `⟨Ind θ, χ⟩ = ⟨θ, χ|_K⟩ = 0`
    have h2 : Work.CharCore.cfInner (Work.Induction.indFun (Kn K) θ) χ = 0 := by
      have hs := Work.CharCore.cfInner_conj_symm χ (Work.Induction.indFun (Kn K) θ)
      rw [hzero] at hs
      exact star_eq_zero.mp hs.symm
    have h3 : Work.CharCore.cfInner θ (Work.Clifford.resFun (Kn K) χ) = 0 := by
      have hrec := Work.Induction.frobenius_reciprocity (Kn K) θ χ
        (Work.CharCore.isClassFun_of_mem_Irr hχIrr)
      rw [h2] at hrec
      exact hrec.symm
    have h4 : Work.CharCore.cfInner (Work.Clifford.resFun (Kn K) χ) θ = 0 := by
      have hs := Work.CharCore.cfInner_conj_symm (Work.Clifford.resFun (Kn K) χ) θ
      rw [h3, map_zero] at hs
      exact hs
    exact hpair h4
  by_contra hne
  have horth := Work.CharCore.irr_orthonormal χ (Work.Induction.indFun (Kn K) θ) hχIrr hIndIrr
  rw [horth, ite_eq_right hne] at hpair'
  exact hpair' rfl

/-! ## Vanishing and degree of members of `𝒮` -/

/-- Members of `𝒮` vanish off `K` (they are induced from `K`). -/
lemma scriptS_vanish (K : Subgroup W)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) ≤ K)
    {χ : ↥(nrm K) → ℂ} (hχ : χ ∈ scriptS K) {x : ↥(nrm K)} (hx : (x : W) ∉ K) :
    χ x = 0 := by
  obtain ⟨θ, -, -, hχeq⟩ := scriptS_eq_induced K hcent hχ
  rw [hχeq, Work.Induction.indFun_apply_def]
  rw [Finset.sum_eq_zero (fun y _ => ?_), mul_zero]
  by_cases hy : y * x * y⁻¹ ∈ Kn K
  · rw [dite_eq_left hy]
    exfalso
    apply hx
    have hmem : x ∈ Kn K := by
      have h := (inferInstance : (Kn K).Normal).conj_mem' (y * x * y⁻¹) hy y
      convert h using 1
      group
    exact (Subgroup.mem_subgroupOf).mp hmem
  · rw [dite_eq_right hy]

/-- Members of `ℤ[𝒮]` vanish off `K`. -/
lemma zSpan_scriptS_vanish (K : Subgroup W)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) ≤ K)
    {α : ↥(nrm K) → ℂ} (hα : α ∈ Work.Coherence.ZSpan (scriptS K))
    {x : ↥(nrm K)} (hx : (x : W) ∉ K) : α x = 0 := by
  obtain ⟨c, rfl⟩ := hα
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_eq_zero fun y _ => by rw [scriptS_vanish K hcent y.2 hx, mul_zero]

/-- Members of `ℤ[𝒮]` are class functions. -/
lemma isClassFun_of_mem_zSpan_scriptS (K : Subgroup W)
    {α : ↥(nrm K) → ℂ} (hα : α ∈ Work.Coherence.ZSpan (scriptS K)) :
    Work.CharCore.IsClassFun α := by
  obtain ⟨c, rfl⟩ := hα
  refine Work.CharCore.IsClassFun.sum _ _ (fun x _ => ?_)
  exact Work.CharCore.IsClassFun.smul _
    (Work.CharCore.isClassFun_of_mem_Irr ((mem_scriptS K).mp x.2).1)

/-- Every member of `𝒮` has degree `[N_W(K) : K]`. -/
lemma scriptS_degree (K : Subgroup W)
    (hKcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) ≤ K)
    {χ : ↥(nrm K) → ℂ} (hχ : χ ∈ scriptS K) : χ 1 = ((Kn K).index : ℂ) := by
  obtain ⟨θ, hθIrr, -, hχeq⟩ := scriptS_eq_induced K hcent hχ
  haveI : IsMulCommutative ↥(Kn K) :=
    isMulCommutative_iff.mpr (fun (a b : ↥(Kn K)) =>
      Subtype.ext (Subtype.ext (hKcomm (a : W) a.2 (b : W) b.2)))
  rw [hχeq, Work.Induction.indFun_apply_one, Work.CharCore.irrDeg_spec hθIrr,
    Work.CharCore.irrDeg_eq_one_of_commutative hθIrr, Nat.cast_one, mul_one]

/-! ## The Brauer–Suzuki isometry -/

/-- **The Dade/Brauer–Suzuki isometry** `⟨α^W, β^W⟩_W = ⟨α, β⟩_N` for `α, β ∈ ℤ[𝒮]⁰`, where
`N = N_W(K)`: elements of `ℤ[𝒮]⁰` are class functions supported in `K \ {1}`, so the general
TI-set isometry applies to the TI set `K \ {1}` with normalizer `N`. -/
lemma isometryOn_scriptS (K : Subgroup W)
    (hTI : ∀ g : W, g ∉ nrm K → K ⊓ Submission.Blueprint.conj g K = ⊥)
    (hKcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) ≤ K) :
    Work.Coherence.IsometryOn (scriptS K) (indLinK K) := by
  refine ⟨fun α hα β hβ => ?_⟩
  have hα' := (Work.Coherence.mem_zSpan0).mp hα
  have hβ' := (Work.Coherence.mem_zSpan0).mp hβ
  have hαsup : Work.BrauerSuzuki.SupportLeSub α ((K : Set W) \ {1}) := by
    intro x hx
    by_cases hxK : (x : W) ∈ K
    · have hx1 : x = 1 := by
        refine Subtype.ext ?_
        by_contra hne
        exact hx ⟨hxK, by simpa [Set.mem_singleton_iff] using hne⟩
      rw [hx1]; exact hα'.2
    · exact zSpan_scriptS_vanish K hcent hα'.1 hxK
  have hβsup : Work.BrauerSuzuki.SupportLeSub β ((K : Set W) \ {1}) := by
    intro x hx
    by_cases hxK : (x : W) ∈ K
    · have hx1 : x = 1 := by
        refine Subtype.ext ?_
        by_contra hne
        exact hx ⟨hxK, by simpa [Set.mem_singleton_iff] using hne⟩
      rw [hx1]; exact hβ'.2
    · exact zSpan_scriptS_vanish K hcent hβ'.1 hxK
  exact Work.BrauerSuzuki.TI.cfInner_indFun_eq_of_TISet (isTISet K hTI hKcomm hcent)
    (isClassFun_of_mem_zSpan_scriptS K hα'.1) (isClassFun_of_mem_zSpan_scriptS K hβ'.1)
    hαsup hβsup

/-! ## The virtual character `(χ - x₀)^W` -/

/-- `(χ - x₀)^W` is a virtual character (a difference of two induced genuine characters). -/
lemma isVChar_indLin_sub (K : Subgroup W) {χ x₀ : ↥(nrm K) → ℂ}
    (hχ : χ ∈ scriptS K) (hx₀ : x₀ ∈ scriptS K) :
    Work.Coherence.IsVChar (indLinK K (χ - x₀)) := by
  rw [map_sub]
  refine (Work.CharCore.IsVChar_iff_coherence _).mp (Work.CharCore.IsVChar.sub ?_ ?_)
  · exact Work.Induction.isVChar_indFun
      (Work.CharCore.IsVChar.of_mem_Irr ((mem_scriptS K).mp hχ).1)
  · exact Work.Induction.isVChar_indFun
      (Work.CharCore.IsVChar.of_mem_Irr ((mem_scriptS K).mp hx₀).1)

/-- `(χ - x₀)^W` has degree zero. -/
lemma indLin_sub_apply_one (K : Subgroup W) (χ x₀ : ↥(nrm K) → ℂ) :
    (indLinK K (χ - x₀)) 1 = ((nrm K).index : ℂ) * ((χ - x₀) 1) := by
  change Work.Induction.indFun (nrm K) (χ - x₀) 1 = ((nrm K).index : ℂ) * ((χ - x₀) 1)
  rw [Work.Induction.indFun_apply_one]

/-! ## The case `|𝒮| ≤ 1` -/

/-- **Coherence is trivial for sets of at most one irreducible character.**  If `S ⊆ Irr H` and
`S.card ≤ 1`, then `ZSpan0 S = 0` (there is at most one summand, of non-zero degree), so the
isometry condition on `ℤ[S]⁰` is vacuous and the lift `φ x = 1_G` (the constant function, a virtual
character, with `⟨1_G, 1_G⟩ = 1`) satisfies the extension lemma
`Work.Coherence.coherent_of_isometry_extension`. -/
lemma coherent_of_card_le_one {H G : Type*} [Group H] [Fintype H] [Group G] [Fintype G]
    {S : Finset (H → ℂ)} (τ : (H → ℂ) →ₗ[ℤ] (G → ℂ))
    (hS : ↑S ⊆ Work.Coherence.Irr H) (hdeg : ∀ x ∈ S, x 1 ≠ 0) (hcard : S.card ≤ 1) :
    Work.Coherence.Coherent S τ := by
  rcases Finset.eq_empty_or_nonempty S with h0 | ⟨χ, hχmem⟩
  · rw [h0]; exact Work.Coherence.coherent_empty
  · have huniq : S = {χ} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hχmem, fun y hy => ?_⟩
      by_contra hne
      have h2 : 2 ≤ S.card := by
        have hsub : ({χ, y} : Finset (H → ℂ)) ⊆ S := by
          intro z hz
          rw [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        calc (2 : ℕ) = ({χ, y} : Finset (H → ℂ)).card :=
              (Finset.card_pair (a := χ) (b := y) (Ne.symm hne)).symm
          _ ≤ S.card := Finset.card_le_card hsub
      omega
    subst huniq
    have hχirr : χ ∈ Work.Coherence.Irr H := hS (by simp)
    have hχ1 : χ 1 ≠ 0 := hdeg χ (by simp)
    have hSorth : Work.Coherence.Orthonormal ({χ} : Finset (H → ℂ)) :=
      Work.Coherence.irr_orthonormal_finset (fun z hz => hS (by simpa using hz))
    -- `ℤ[{χ}]⁰ = 0`
    have hzero : ∀ α ∈ Work.Coherence.ZSpan0 ({χ} : Finset (H → ℂ)), α = 0 := by
      intro α hα
      obtain ⟨hc, hα1⟩ := (Work.Coherence.mem_zSpan0).mp hα
      obtain ⟨c, hc'⟩ := (Work.Coherence.mem_zSpan).mp hc
      have hsum_eq : (∑ x : ↥({χ} : Finset (H → ℂ)),
            (c x : ℂ) • ((x : ↥({χ} : Finset (H → ℂ))) : H → ℂ))
          = (c ⟨χ, Finset.mem_singleton_self χ⟩ : ℂ) • χ := by
        refine Finset.sum_eq_single (⟨χ, Finset.mem_singleton_self χ⟩ :
          ↥({χ} : Finset (H → ℂ))) ?_ ?_
        · intro b _ hb
          exact absurd (Subsingleton.elim b _) hb
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
      have hval : (c ⟨χ, Finset.mem_singleton_self χ⟩ : ℂ) = 0 := by
        have h := congrFun (hc'.trans hsum_eq) 1
        rw [hα1, Pi.smul_apply, smul_eq_mul] at h
        rcases mul_eq_zero.mp h.symm with h' | h'
        · exact h'
        · exact absurd h' hχ1
      rw [hc', hsum_eq, hval, zero_smul]
    refine Work.Coherence.coherent_of_isometry_extension (x₀ := χ) hSorth (by simp)
      (fun x hx => by rw [Finset.mem_singleton.mp hx]) hχ1 ?_
      (φ := fun _ => (1 : G → ℂ)) ?_ ?_ ?_
    · refine ⟨fun α hα β hβ => ?_⟩
      rw [hzero α hα, hzero β hβ]
      simp
    · intro x hx
      rw [Finset.mem_singleton.mp hx]
      have h1 : Work.Coherence.cfInner (1 : G → ℂ) (1 : G → ℂ) = 1 := by
        rw [Work.Coherence.cfInner_apply]
        simp
      have h2 : Work.Coherence.cfInner χ χ = 1 := by
        rw [Work.Coherence.irr_cfInner hχirr hχirr]; simp
      rw [h1, h2]
    · intro x hx
      rw [Finset.mem_singleton.mp hx]
    · intro x hx
      refine (Work.CharCore.IsVChar_iff_coherence _).mp
        (Work.CharCore.IsVChar.of_mem_Irr (Work.CharCore.principalChar_mem_Irr))

/-! ## Instance transfer

`Work.Coherence.Coherent` depends on the chosen `Fintype` instance on the subgroup only through
`cfInner`, which is instance-independent (`Work.FeitSibley.CharQ.cfInner_fintype_indep`).  This
lets us move a coherence statement between different instances. -/

/-- `IsometryOnAll` is insensitive to the chosen `Fintype` instances. -/
theorem isometryOnAll_fintype_indep {H G : Type*} [Group H]
    {i j : Fintype H} {iG jG : Fintype G}
    {S : Finset (H → ℂ)} {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (h : @Work.Coherence.IsometryOnAll G H i iG S τ) :
    @Work.Coherence.IsometryOnAll G H j jG S τ := by
  obtain ⟨h2⟩ := h
  exact ⟨fun α hα β hβ => by
    calc @Work.Coherence.cfInner G jG (τ α) (τ β)
        = @Work.Coherence.cfInner G iG (τ α) (τ β) :=
          Work.FeitSibley.CharQ.cfInner_fintype_indep jG iG (τ α) (τ β)
      _ = @Work.Coherence.cfInner H i α β := h2 α hα β hβ
      _ = @Work.Coherence.cfInner H j α β :=
          (Work.FeitSibley.CharQ.cfInner_fintype_indep j i α β).symm⟩

/-- `Coherent` is insensitive to the chosen `Fintype` instances. -/
theorem coherent_fintype_indep {H G : Type*} [Group H] [Group G]
    (iH jH : Fintype H) (iG jG : Fintype G)
    {S : Finset (H → ℂ)} {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (h : @Work.Coherence.Coherent G H _ iH _ iG S τ) :
    @Work.Coherence.Coherent G H _ jH _ jG S τ := by
  obtain ⟨τ', h1, h2, h3⟩ := h
  exact ⟨τ', h1, isometryOnAll_fintype_indep h2, h3⟩

/-! ## The main theorem -/

theorem exc_char_coherent {W : Type} [Group W] [Fintype W] (K : Subgroup W) [Fintype ↥K]
    [Fintype ↥(Subgroup.normalizer (K : Set W))]
    (hTI : ∀ g : W, g ∉ Subgroup.normalizer (K : Set W) →
      K ⊓ Submission.Blueprint.conj g K = ⊥)
    (hKcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) ≤ K) :
    Work.Coherence.Coherent
      (Submission.Blueprint.excludingKernel (Subgroup.normalizer (K : Set W)) K)
      (Submission.Blueprint.indLinear (Subgroup.normalizer (K : Set W))) := by
  -- work with the canonical `Fintype` instance on `N_W(K)` throughout
  letI : Fintype ↥(nrm K) := instNrm K
  have main : Work.Coherence.Coherent (scriptS K) (indLinK K) := by
    by_cases hcard : 2 ≤ (scriptS K).card
    · obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp (by omega : 0 < (scriptS K).card)
      have hdeg : ∀ x ∈ scriptS K, x 1 = x₀ 1 := fun x hx =>
        (scriptS_degree K hKcomm hcent hx).trans (scriptS_degree K hKcomm hcent hx₀).symm
      have hx₀1 : x₀ 1 ≠ 0 := by
        rw [scriptS_degree K hKcomm hcent hx₀]
        exact_mod_cast Subgroup.index_ne_zero_of_finite (H := Kn K)
      refine Work.Coherence.coherent_of_norm_two_lift (orthonormal_scriptS K) hx₀ hdeg hx₀1
        (isometryOn_scriptS K hTI hKcomm hcent) (fun x hx => isVChar_indLin_sub K hx hx₀)
        (fun x hx => ?_) hcard
      rw [indLin_sub_apply_one K x x₀, Pi.sub_apply, hdeg x hx, sub_self, mul_zero]
    · refine coherent_of_card_le_one (indLinK K) ?_ ?_ (by omega)
      · intro x hx
        exact (Work.CharCore.mem_Irr_iff_coherence).mp ((mem_scriptS K).mp hx).1
      · intro x hx
        rw [scriptS_degree K hKcomm hcent hx]
        exact_mod_cast Subgroup.index_ne_zero_of_finite (H := Kn K)
  exact coherent_fintype_indep (instNrm K) _ _ _ main

end

end Work.ZassenhausPSL2
