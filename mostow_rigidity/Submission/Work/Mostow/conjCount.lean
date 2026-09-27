import Mathlib
import Submission.Work.Mostow.gapA.conjCount3
import Submission.Work.Mostow.nearId_norm
import Submission.Work.Mostow.near1_unitBall
import Submission.Work.Mostow.Margulis.ComplexifyOrth
import Submission.Work.Mostow.Margulis.cActHom_isSemisimple
import Submission.Work.Mostow.StabLift
import Submission.Work.Mostow.zassenhausNilpotent
import Submission.Work.Mostow.Margulis.near1NearId
import Submission.Work.Mostow.finiteClosureNearIdAt
import Submission.Work.Mostow.linPartExists
import Submission.Work.Mostow.conjCountCard
import Submission.Work.Mostow.isomNormTrace
import Submission.Work.Mostow.linPartBundle

/-!
# ConjCount: the number of conjugates of `b` that are near-identity at a point is bounded
-/

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

namespace Work.Mostow

set_option maxHeartbeats 2000000

noncomputable section

variable {n : ℕ}

/-! ## Temporary placeholders for the delegated lemmas (replaced by imports at the end) -/

/-! ## Conjugation covariance of `NearIdAt` -/

lemma nearIdAt_conj_point (hA : POActionProp n) (hI : HypIsometryProp n)
    (C γ : PO n 1) (u : E n) (η : ℝ) :
    NearIdAt (C⁻¹ * γ * C) u η ↔ NearIdAt γ (C • u) η := by
  have hone : ∀ u : E n, (1 : PO n 1) • u = u := hA.2.2.2.1
  have hmul : ∀ (g h : PO n 1) (u : E n), (g * h) • u = g • (h • u) := hA.2.2.2.2.1
  have hisom : ∀ (g : PO n 1) (u v : E n), hdist (g • u) (g • v) = hdist u v :=
    hI.2.2.2.2.2.2.1
  have hCin : ∀ v : E n, C • (C⁻¹ • v) = v := by
    intro v
    rw [← hmul C C⁻¹ v, mul_inv_cancel, hone]
  have hconj : ∀ v : E n, (C⁻¹ * γ * C) • v = C⁻¹ • (γ • (C • v)) := by
    intro v
    rw [hmul (C⁻¹ * γ) C v, hmul C⁻¹ γ (C • v)]
  constructor
  · intro h v hv
    have hv' : hdist u (C⁻¹ • v) ≤ 1 := by
      have : hdist u (C⁻¹ • v) = hdist (C • u) v := by
        rw [← hisom C u (C⁻¹ • v), hCin v]
      rw [this]; exact hv
    have h1 := h (C⁻¹ • v) hv'
    rw [hconj (C⁻¹ • v), hCin v] at h1
    have h3 : hdist (C⁻¹ • v) (C⁻¹ • (γ • v)) = hdist v (γ • v) := by
      rw [← hisom C (C⁻¹ • v) (C⁻¹ • (γ • v)), hCin v, hCin (γ • v)]
    linarith [h1, h3.le, h3.ge]
  · intro h v hv
    have hv' : hdist (C • u) (C • v) ≤ 1 := by
      rw [hisom C u v]; exact hv
    have h1 := h (C • v) hv'
    have h3 : hdist v ((C⁻¹ * γ * C) • v) = hdist (C • v) (γ • (C • v)) := by
      rw [hconj v]
      rw [← hisom C v (C⁻¹ • (γ • (C • v))), hCin (γ • (C • v))]
    linarith [h1, h3.le, h3.ge]

/-! ## Smallness at fixed points -/

theorem smallAt (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (θ : ℝ) (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (g : PO n 1) (w p : E n), (∃ q : E n, g • q = q) → g • p = p →
      NearIdAt g w δ → NearIdAt g p θ := by
  obtain ⟨Ctr, hCtrpos, hCtr⟩ := (isomNormTrace n hA hI).2
  obtain ⟨q, hqpos, hq⟩ := Margulis.near1NearId n hn hA hI θ hθ
  have hCtr1 : 0 < Ctr + 1 := by linarith
  set δ : ℝ := min 1 (q ^ 2 / (2 * (Ctr + 1))) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min one_pos (div_pos (pow_pos hqpos 2) (by linarith))
  have hδ1 : δ ≤ 1 := by rw [hδdef]; exact min_le_left _ _
  have hδq : 2 * Ctr * δ ≤ q ^ 2 := by
    have h1 : δ ≤ q ^ 2 / (2 * (Ctr + 1)) := by rw [hδdef]; exact min_le_right _ _
    have h5 : 2 * Ctr * δ ≤ 2 * Ctr * (q ^ 2 / (2 * (Ctr + 1))) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have h6 : 2 * Ctr * (q ^ 2 / (2 * (Ctr + 1))) ≤ q ^ 2 := by
      rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
      nlinarith [hCtrpos, sq_nonneg q]
    linarith [h5, h6]
  refine ⟨δ, hδpos, ?_⟩
  intro g w p hell hpfix hnear
  have hone : ∀ u : E n, (1 : PO n 1) • u = u := hA.2.2.2.1
  have hmul : ∀ (g h : PO n 1) (u : E n), (g * h) • u = g • (h • u) := hA.2.2.2.2.1
  obtain ⟨B, hB⟩ := (BoostTransitive n hA).1 p
  set h : PO n 1 := B⁻¹ * g * B with hhdef
  have hfix0 : h • (0 : E n) = 0 := by
    have hstep : h • (0 : E n) = B⁻¹ • (g • (B • (0 : E n))) := by
      rw [hhdef, hmul (B⁻¹ * g) B, hmul B⁻¹ g]
    rw [hstep, hB, hpfix]
    have hp0 : B⁻¹ • p = 0 := by
      rw [← hB, ← hmul B⁻¹ B (0 : E n), inv_mul_cancel, hone]
    exact hp0
  obtain ⟨R, hR⟩ := linPartExists n hA hI h hfix0
  obtain ⟨hL1, hL2, hL3, hL4, hL5⟩ := linPartBundle n hA hI h R hR
  have hnear' : NearIdAt h (B⁻¹ • w) δ := by
    have hw : B • (B⁻¹ • w) = w := by rw [← hmul B B⁻¹ w, mul_inv_cancel, hone]
    rw [hhdef]
    refine (nearIdAt_conj_point hA hI B g (B⁻¹ • w) δ).mpr ?_
    rw [hw]; exact hnear
  have htr : |(LambdaMat h).trace - ((n : ℝ) + 1)| ≤ Ctr * δ :=
    hCtr h (B⁻¹ • w) δ hδpos hδ1 hnear'
  have hnorm : ‖(R : E n →L[ℝ] E n) - 1‖ ≤ q := by
    have h1 : ‖(R : E n →L[ℝ] E n) - 1‖ ^ 2 ≤ 2 * ((n : ℝ) - LinearMap.trace ℝ (E n)
        (R : E n →ₗ[ℝ] E n)) := (isomNormTrace n hA hI).1 R
    have h2 : (n : ℝ) + 1 - (LambdaMat h).trace ≤ Ctr * δ := by
      have := abs_le.mp htr
      linarith [this.2]
    have h4 : ‖(R : E n →L[ℝ] E n) - 1‖ ^ 2 ≤ q ^ 2 := by
      have : (n : ℝ) - LinearMap.trace ℝ (E n) (R : E n →ₗ[ℝ] E n)
          = (n : ℝ) + 1 - (LambdaMat h).trace := by linarith [hL3]
      rw [this] at h1
      linarith [h1, h2, hδq]
    calc ‖(R : E n →L[ℝ] E n) - 1‖ = Real.sqrt ((‖(R : E n →L[ℝ] E n) - 1‖) ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (q ^ 2) := Real.sqrt_le_sqrt h4
      _ = q := Real.sqrt_sq hqpos.le
  have hnear1 : Near1 (ToO h) q := hL4 q hnorm
  have hth : NearIdAt h (0 : E n) θ := hq h hnear1
  have hback : NearIdAt (B⁻¹ * g * B) (0 : E n) θ := by
    rw [hhdef] at hth
    exact hth
  exact (gapA.nearIdAt_conj_iff hA hI hB θ g).mp hback


/-! ## Two near-identity elliptic elements commute -/

lemma eq_of_smul_eq (hA : POActionProp n) {g g' : PO n 1} (h : ∀ u : E n, g • u = g' • u) :
    g = g' := by
  have hone : ∀ u : E n, (1 : PO n 1) • u = u := hA.2.2.2.1
  have hmul : ∀ (g h : PO n 1) (u : E n), (g * h) • u = g • (h • u) := hA.2.2.2.2.1
  have h1 : g'⁻¹ * g = 1 := hA.2.2.2.2.2.1 (g'⁻¹ * g) (by
    intro u
    rw [hmul g'⁻¹ g u, h u]
    rw [← hmul g'⁻¹ g' u, inv_mul_cancel, hone])
  calc g = g' * (g'⁻¹ * g) := by group
    _ = g' * 1 := by rw [h1]
    _ = g' := mul_one g'

lemma eq_of_conj_smul_eq (hA : POActionProp n) {B x y : PO n 1}
    (h : ∀ u : E n, (B⁻¹ * x * B) • u = (B⁻¹ * y * B) • u) : x = y := by
  have hone : ∀ u : E n, (1 : PO n 1) • u = u := hA.2.2.2.1
  have hmul : ∀ (g h : PO n 1) (u : E n), (g * h) • u = g • (h • u) := hA.2.2.2.2.1
  have hBinv : ∀ u : E n, B • (B⁻¹ • u) = u := by
    intro u; rw [← hmul B B⁻¹ u, mul_inv_cancel, hone]
  refine eq_of_smul_eq hA (fun u => ?_)
  have h1 := h (B⁻¹ • u)
  have e1 : (B⁻¹ * x * B) • (B⁻¹ • u) = B⁻¹ • (x • u) := by
    rw [hmul (B⁻¹ * x) B, hmul B⁻¹ x, hBinv u]
  have e2 : (B⁻¹ * y * B) • (B⁻¹ • u) = B⁻¹ • (y • u) := by
    rw [hmul (B⁻¹ * y) B, hmul B⁻¹ y, hBinv u]
  rw [e1, e2] at h1
  have h2 := congrArg (fun w => B • w) h1
  rwa [hBinv, hBinv] at h2

/-- Two elements of a discrete group which are near-identity at a common point, both elliptic,
commute provided the near-identity parameter is small. -/
theorem pairCommute (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (θZs θF δ η₁ : ℝ) (hθZspos : 0 < θZs) (hηZs : η₁ ≤ θZs) (hηδ : η₁ ≤ δ)
    (hZass : ∀ (Γ : Subgroup (PO n 1)), IsDiscrete (SetLike.coe Γ) → ∀ z : E n,
      Group.IsNilpotent ↥(Subgroup.closure {γ : Γ | NearIdAt (γ : PO n 1) z θZs}))
    (hθF : ∀ (H : Subgroup (PO n 1)), Finite ↥H → ∀ p : E n, (∀ h ∈ H, h • p = p) →
      ∀ a ∈ H, ∀ c ∈ H, NearIdAt a p θF → NearIdAt c p θF → a * c = c * a)
    (hδ : ∀ (g : PO n 1) (w p : E n), (∃ q : E n, g • q = q) → g • p = p →
      NearIdAt g w δ → NearIdAt g p θF) :
    ∀ (Γ : Subgroup (PO n 1)), IsDiscrete (SetLike.coe Γ) →
      ∀ (w : E n) (a a' : PO n 1), a ∈ Γ → a' ∈ Γ →
      (∃ q : E n, a • q = q) → (∃ q : E n, a' • q = q) →
      NearIdAt a w η₁ → NearIdAt a' w η₁ → a * a' = a' * a := by
  classical
  intro Γ hdisc w a a' ha ha' haell ha'ell haN ha'N
  set S : Finset Γ := ({⟨a, ha⟩, ⟨a', ha'⟩} : Finset Γ) with hSdef
  have hSsub : ∀ σ ∈ S, NearIdAt (σ : PO n 1) w θZs := by
    intro σ hσ
    rw [hSdef, Finset.mem_insert, Finset.mem_singleton] at hσ
    rcases hσ with rfl | rfl
    · exact fun u hu => lt_of_lt_of_le (haN u hu) hηZs
    · exact fun u hu => lt_of_lt_of_le (ha'N u hu) hηZs
  have hSell : ∀ σ ∈ S, ∃ p : E n, (σ : PO n 1) • p = p := by
    intro σ hσ
    rw [hSdef, Finset.mem_insert, Finset.mem_singleton] at hσ
    rcases hσ with rfl | rfl
    · simpa using haell
    · simpa using ha'ell
  haveI hfinH : Finite ↥(Subgroup.closure (↑S : Set Γ)) :=
    finiteClosureNearIdAt n hn hA hI θZs hθZspos hZass Γ hdisc S w hSsub hSell
  set Hp : Subgroup (PO n 1) := (Subgroup.closure (↑S : Set Γ)).map (Subgroup.subtype Γ)
    with hHpdef
  haveI hfinHp : Finite ↥Hp := by
    refine Finite.of_surjective
      (fun x : ↥(Subgroup.closure (↑S : Set Γ)) => (⟨(x : Γ), ⟨x, x.2, rfl⟩⟩ : ↥Hp)) ?_
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  obtain ⟨p, hp⟩ := fixPoint_of_finite hA Hp hfinHp
  have haHp : a ∈ Hp := by
    refine Subgroup.mem_map.mpr ⟨⟨a, ha⟩, ?_, rfl⟩
    exact Subgroup.subset_closure (Finset.mem_coe.mpr (by
      rw [hSdef]; exact Finset.mem_insert_self _ _))
  have ha'Hp : a' ∈ Hp := by
    refine Subgroup.mem_map.mpr ⟨⟨a', ha'⟩, ?_, rfl⟩
    exact Subgroup.subset_closure (Finset.mem_coe.mpr (by
      rw [hSdef]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  have hnear_a : NearIdAt a p θF :=
    hδ a w p haell (hp a haHp) (fun u hu => lt_of_lt_of_le (haN u hu) hηδ)
  have hnear_a' : NearIdAt a' p θF :=
    hδ a' w p ha'ell (hp a' ha'Hp) (fun u hu => lt_of_lt_of_le (ha'N u hu) hηδ)
  exact hθF Hp hfinHp p hp a haHp a' ha'Hp hnear_a hnear_a'



/-! ## ConjCount -/

theorem conjCount (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n) :
    ∃ η₁ : ℝ, 0 < η₁ ∧ ∃ C : ℕ, ∀ Γ : Subgroup (PO n 1), IsDiscrete (SetLike.coe Γ) →
      ∀ b ∈ Γ, (∃ p : E n, b • p = p) → ∀ w : E n, NearIdAt b w η₁ →
        {c : PO n 1 | NearIdAt c w η₁ ∧ ∃ γ ∈ Γ, c = γ⁻¹ * b * γ}.Finite ∧
        {c : PO n 1 | NearIdAt c w η₁ ∧ ∃ γ ∈ Γ, c = γ⁻¹ * b * γ}.ncard ≤ C := by
  classical
  obtain ⟨θZ, hθZpos, hθZ⟩ := gapA.nilpotentPairNearIdAt n hn hA hI
  obtain ⟨θF, hθFpos, hθF⟩ := frobeniusCommute n hn hA hI
  obtain ⟨δ, hδpos, hδ⟩ := smallAt n hn hA hI θF hθFpos
  obtain ⟨θZs, hθZspos, hθZs⟩ := zassenhausNilpotent n hn hA hI
  set η₀ : ℝ := min (min θZ δ) (min θZs 1) with hη₀def
  have hη₀pos : 0 < η₀ := by
    rw [hη₀def]; exact lt_min (lt_min hθZpos hδpos) (lt_min hθZspos one_pos)
  have hη₀Z : η₀ ≤ θZ := by rw [hη₀def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hη₀δ : η₀ ≤ δ := by rw [hη₀def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hη₀Zs : η₀ ≤ θZs := by rw [hη₀def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  refine ⟨η₀, hη₀pos, (n + 2) ^ (2 * n + 1), ?_⟩
  intro Γ hdisc b hb hbFix w hbN
  have hone : ∀ u : E n, (1 : PO n 1) • u = u := hA.2.2.2.1
  have hmul : ∀ (g h : PO n 1) (u : E n), (g * h) • u = g • (h • u) := hA.2.2.2.2.1
  obtain ⟨p0, hp0⟩ := hbFix
  have hbtor : IsOfFinOrder b := gapA.isOfFinOrder_of_fixes_point n hA hI Γ hdisc b hb p0 hp0
  have key : ∀ F : Finset (PO n 1),
      (∀ c ∈ F, NearIdAt c w η₀ ∧ ∃ γ ∈ Γ, c = γ⁻¹ * b * γ) →
      F.card ≤ (n + 2) ^ (2 * n + 1) := by
    intro F hF
    set F' : Finset (PO n 1) := insert b F with hF'def
    have hTnear : ∀ c ∈ F, NearIdAt c w η₀ := fun c hc => (hF c hc).1
    have hTconj : ∀ c ∈ F, ∃ γ ∈ Γ, c = γ⁻¹ * b * γ := fun c hc => (hF c hc).2
    have hF'conj : ∀ c ∈ F', ∃ γ ∈ Γ, c = γ⁻¹ * b * γ := by
      intro c hc
      rw [hF'def, Finset.mem_insert] at hc
      rcases hc with rfl | hc
      · exact ⟨1, Γ.one_mem, by simp⟩
      · exact hTconj c hc
    have hF'sub : ∀ c ∈ F', c ∈ Γ := by
      intro c hc
      rw [hF'def, Finset.mem_insert] at hc
      rcases hc with rfl | hc
      · exact hb
      · obtain ⟨γ, hγ, hceq⟩ := hTconj c hc
        rw [hceq]
        exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) hb) hγ
    have hF'near : ∀ c ∈ F', NearIdAt c w η₀ := by
      intro c hc
      rw [hF'def, Finset.mem_insert] at hc
      rcases hc with rfl | hc
      · exact hbN
      · exact hTnear c hc
    have hF'tor : ∀ c ∈ F', IsOfFinOrder c := by
      intro c hc
      rw [hF'def, Finset.mem_insert] at hc
      rcases hc with rfl | hc
      · exact hbtor
      · obtain ⟨γ, hγ, hceq⟩ := hTconj c hc
        rw [hceq]
        obtain ⟨k, hkpos, hk⟩ := isOfFinOrder_iff_pow_eq_one.mp hbtor
        refine isOfFinOrder_iff_pow_eq_one.mpr ⟨k, hkpos, ?_⟩
        have hconj : (γ⁻¹ * b * γ) = (MulAut.conj γ⁻¹) b := by
          rw [MulAut.conj_apply]; simp
        rw [hconj, ← map_pow, hk, map_one]
    have hF'ell : ∀ c ∈ F', ∃ p : E n, c • p = p := by
      intro c hc
      rw [hF'def, Finset.mem_insert] at hc
      rcases hc with rfl | hc
      · exact ⟨p0, hp0⟩
      · obtain ⟨γ, hγ, hceq⟩ := hTconj c hc
        refine ⟨γ⁻¹ • p0, ?_⟩
        have hγinv : γ • (γ⁻¹ • p0) = p0 := by
          rw [← hmul γ γ⁻¹ p0, mul_inv_cancel, hone]
        rw [hceq, hmul, hmul, hγinv, hp0]
    have hF'comm : ∀ c ∈ F', ∀ c' ∈ F', c * c' = c' * c := fun c hc c' hc' =>
      pairCommute n hn hA hI θZs θF δ η₀ hθZspos hη₀Zs hη₀δ hθZs hθF hδ Γ hdisc w c c'
        (hF'sub c hc) (hF'sub c' hc') (hF'ell c hc) (hF'ell c' hc')
        (hF'near c hc) (hF'near c' hc')
    -- the finite subgroup generated by `F'` inside `Γ`
    let G : Finset Γ := F'.attach.image (fun c => (⟨c.1, hF'sub c.1 c.2⟩ : Γ))
    have hGnear : ∀ σ ∈ G, NearIdAt (σ : PO n 1) w θZs := by
      intro σ hσ
      obtain ⟨c, hc, hcσ⟩ := Finset.mem_image.mp hσ
      rw [← hcσ]
      exact fun u hu => lt_of_lt_of_le (hF'near c.1 c.2 u hu) hη₀Zs
    have hGell : ∀ σ ∈ G, ∃ p : E n, (σ : PO n 1) • p = p := by
      intro σ hσ
      obtain ⟨c, hc, hcσ⟩ := Finset.mem_image.mp hσ
      rw [← hcσ]
      exact hF'ell c.1 c.2
    haveI hfinHG : Finite ↥(Subgroup.closure (↑G : Set Γ)) :=
      finiteClosureNearIdAt n hn hA hI θZs hθZspos hθZs Γ hdisc G w hGnear hGell
    set Hp : Subgroup (PO n 1) := (Subgroup.closure (↑G : Set Γ)).map (Subgroup.subtype Γ)
      with hHpdef
    haveI hfinHp : Finite ↥Hp := by
      refine Finite.of_surjective
        (fun x : ↥(Subgroup.closure (↑G : Set Γ)) => (⟨(x : Γ), ⟨x, x.2, rfl⟩⟩ : ↥Hp)) ?_
      intro y
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    obtain ⟨p, hp⟩ := fixPoint_of_finite hA Hp hfinHp
    have hpF' : ∀ c ∈ F', c • p = p := by
      intro c hc
      apply hp
      refine Subgroup.mem_map.mpr ⟨⟨c, hF'sub c hc⟩, ?_, rfl⟩
      exact Subgroup.subset_closure (Finset.mem_coe.mpr (Finset.mem_image.mpr
        ⟨⟨c, hc⟩, Finset.mem_attach F' ⟨c, hc⟩, rfl⟩))
    -- the boost at `p` and the linear parts
    obtain ⟨B, hB⟩ := (BoostTransitive n hA).1 p
    have hfix0 : ∀ c ∈ F', (B⁻¹ * c * B) • (0 : E n) = 0 := by
      intro c hc
      have hstep : (B⁻¹ * c * B) • (0 : E n) = B⁻¹ • (c • (B • (0 : E n))) := by
        rw [hmul (B⁻¹ * c) B, hmul B⁻¹ c]
      rw [hstep, hB, hpF' c hc]
      rw [← hB, ← hmul B⁻¹ B (0 : E n), inv_mul_cancel, hone]
    have hRex : ∀ c ∈ F', ∃ R : E n ≃ₗᵢ[ℝ] E n, ∀ u : E n, (B⁻¹ * c * B) • u = R u :=
      fun c hc => linPartExists n hA hI _ (hfix0 c hc)
    let Rof : ↥F' → E n ≃ₗᵢ[ℝ] E n := fun c => Classical.choose (hRex c.1 c.2)
    have hRof : ∀ (c : ↥F') (u : E n), (B⁻¹ * c.1 * B) • u = Rof c u :=
      fun c => Classical.choose_spec (hRex c.1 c.2)
    let A' : Finset (E n ≃ₗᵢ[ℝ] E n) := F'.attach.image Rof
    have hinjRof : Function.Injective Rof := by
      intro x y hxy
      have hact : ∀ u : E n, (B⁻¹ * x.1 * B) • u = (B⁻¹ * y.1 * B) • u := by
        intro u
        rw [hRof x u, hRof y u, hxy]
      exact Subtype.ext (eq_of_conj_smul_eq hA hact)
    have hA'card : A'.card = F'.card := by
      have h := Finset.card_image_of_injective (f := Rof) F'.attach hinjRof
      rw [Finset.card_attach] at h
      exact h
    -- the spectrum bound
    let Mb : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ := (LambdaMat b).map (algebraMap ℝ ℂ)
    let Sb : Finset ℂ := (Matrix.charpoly Mb).roots.toFinset
    have hScard : Sb.card ≤ n + 1 := by
      have h1 : Sb.card ≤ (Matrix.charpoly Mb).roots.card := Multiset.toFinset_card_le _
      have h2 : (Matrix.charpoly Mb).roots.card ≤ (Matrix.charpoly Mb).natDegree :=
        Polynomial.card_roots' _
      have h3 : (Matrix.charpoly Mb).natDegree = n + 1 := by
        rw [Matrix.charpoly_natDegree_eq_dim]; simp
      omega
    have hspec : ∀ a ∈ A', ∀ μ : ℂ,
        Module.End.HasEigenvalue ((Margulis.cAct a : (E n × E n) →ₗ[ℂ] (E n × E n))) μ →
        μ ∈ Sb := by
      intro a ha μ hμ
      obtain ⟨c, hc, hac⟩ := Finset.mem_image.mp ha
      rw [← hac] at hμ
      obtain ⟨-, -, -, -, hL5⟩ := linPartBundle n hA hI (B⁻¹ * c.1 * B) (Rof c) (hRof c)
      have hroot : (Matrix.charpoly ((LambdaMat (B⁻¹ * c.1 * B)).map (algebraMap ℝ ℂ))).IsRoot μ :=
        hL5 μ hμ
      have hchar : (Matrix.charpoly ((LambdaMat (B⁻¹ * c.1 * B)).map (algebraMap ℝ ℂ)))
          = (Matrix.charpoly Mb) := by
        obtain ⟨γ, hγ, hceq⟩ := hF'conj c.1 c.2
        have hinvB : LambdaMat B⁻¹ * LambdaMat B = 1 := by
          rw [← LambdaMat_mul hA, inv_mul_cancel, LambdaMat_one hA]
        have hinvB' : LambdaMat B * LambdaMat B⁻¹ = 1 := by
          rw [← LambdaMat_mul hA, mul_inv_cancel, LambdaMat_one hA]
        have hinvγ : LambdaMat γ⁻¹ * LambdaMat γ = 1 := by
          rw [← LambdaMat_mul hA, inv_mul_cancel, LambdaMat_one hA]
        have hinvγ' : LambdaMat γ * LambdaMat γ⁻¹ = 1 := by
          rw [← LambdaMat_mul hA, mul_inv_cancel, LambdaMat_one hA]
        have hLc : LambdaMat c.1 = LambdaMat γ⁻¹ * LambdaMat b * LambdaMat γ := by
          rw [hceq, LambdaMat_mul hA, LambdaMat_mul hA]
        have hLB : LambdaMat (B⁻¹ * c.1 * B) = LambdaMat B⁻¹ * LambdaMat c.1 * LambdaMat B := by
          rw [LambdaMat_mul hA, LambdaMat_mul hA]
        have eqB : LambdaMat (B⁻¹ * c.1 * B)
            = (LambdaMat B⁻¹ * LambdaMat γ⁻¹) * LambdaMat b * (LambdaMat γ * LambdaMat B) := by
          rw [hLB, hLc]; noncomm_ring
        have eqinv : (LambdaMat γ * LambdaMat B) * (LambdaMat B⁻¹ * LambdaMat γ⁻¹) = 1 := by
          have hstep : (LambdaMat γ * LambdaMat B) * (LambdaMat B⁻¹ * LambdaMat γ⁻¹)
              = LambdaMat γ * (LambdaMat B * LambdaMat B⁻¹) * LambdaMat γ⁻¹ := by noncomm_ring
          rw [hstep, hinvB']
          simp [hinvγ']
        set X : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ :=
          (LambdaMat γ * LambdaMat B).map (algebraMap ℝ ℂ) with hX
        set Y : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ :=
          (LambdaMat B⁻¹ * LambdaMat γ⁻¹).map (algebraMap ℝ ℂ) with hY
        have hmap (M N : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) :
            (M * N).map (algebraMap ℝ ℂ) = M.map (algebraMap ℝ ℂ) * N.map (algebraMap ℝ ℂ) :=
          Matrix.map_mul
        have hXY : X * Y = 1 := by
          rw [hX, hY, ← hmap, eqinv]
          rw [Matrix.map_one]
          · exact map_zero _
          · exact map_one _
        have hexp : (LambdaMat (B⁻¹ * c.1 * B)).map (algebraMap ℝ ℂ) = Y * Mb * X := by
          rw [eqB, hX, hY]
          simp only [Matrix.map_mul]
          noncomm_ring
        rw [hexp]
        have hcycle : Matrix.charpoly (Y * Mb * X) = Mb.charpoly := by
          rw [show Y * Mb * X = (Y * Mb) * X from rfl, Matrix.charpoly_mul_comm (Y * Mb) X]
          have h2 : X * (Y * Mb) = Mb := by rw [← mul_assoc, hXY, one_mul]
          rw [h2]
        rw [hcycle]
      rw [hchar] at hroot
      change μ ∈ (Matrix.charpoly Mb).roots.toFinset
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (Matrix.charpoly_monic Mb).ne_zero]
      exact hroot
    have hcommA : ∀ a ∈ A', ∀ a' ∈ A', a * a' = a' * a := by
      intro a ha a' ha'
      obtain ⟨c, hc, hac⟩ := Finset.mem_image.mp ha
      obtain ⟨d, hd, had⟩ := Finset.mem_image.mp ha'
      rw [← hac, ← had]
      have hcd : c.1 * d.1 = d.1 * c.1 := hF'comm c.1 c.2 d.1 d.2
      ext u
      have e1 : (Rof c * Rof d) u = (B⁻¹ * (c.1 * d.1) * B) • u := by
        show Rof c (Rof d u) = _
        rw [← hRof c (Rof d u), ← hRof d u]
        rw [← hmul (B⁻¹ * c.1 * B) (B⁻¹ * d.1 * B) u]
        congr 1
        group
      have e2 : (Rof d * Rof c) u = (B⁻¹ * (d.1 * c.1) * B) • u := by
        show Rof d (Rof c u) = _
        rw [← hRof d (Rof c u), ← hRof c u]
        rw [← hmul (B⁻¹ * d.1 * B) (B⁻¹ * c.1 * B) u]
        congr 1
        group
      rw [e1, e2, hcd]
    have hcardA := conjCountCard n Sb A' hcommA hspec
    rw [hA'card] at hcardA
    have hcardF' : F.card ≤ F'.card := by
      rw [hF'def]
      exact Finset.card_le_card (Finset.subset_insert b F)
    calc F.card ≤ F'.card := hcardF'
      _ ≤ (Sb.card + 1) ^ (2 * n + 1) := hcardA
      _ ≤ ((n + 2)) ^ (2 * n + 1) := by
          apply Nat.pow_le_pow_left
          omega
  constructor
  · by_contra hT
    rw [Set.not_finite] at hT
    obtain ⟨t, ht, htcard⟩ := hT.exists_subset_card_eq ((n + 2) ^ (2 * n + 1) + 1)
    have h1 := key t (fun c hc => ht hc)
    omega
  · have hfin : ({c : PO n 1 | NearIdAt c w η₀ ∧ ∃ γ ∈ Γ, c = γ⁻¹ * b * γ} : Set (PO n 1)).Finite := by
      by_contra hT
      rw [Set.not_finite] at hT
      obtain ⟨t, ht, htcard⟩ := hT.exists_subset_card_eq ((n + 2) ^ (2 * n + 1) + 1)
      have h1 := key t (fun c hc => ht hc)
      omega
    have h2 := key hfin.toFinset (fun c hc => hfin.mem_toFinset.mp hc)
    rwa [Set.ncard_eq_toFinset_card _ hfin]

end

end Work.Mostow
