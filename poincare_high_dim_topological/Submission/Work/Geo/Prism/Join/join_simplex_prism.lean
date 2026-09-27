import Mathlib
import Submission.Work.Geo.Prism.Defs
import Submission.Work.PL.Defs
import Submission.Work.Geo.Prism.Join.exists_affineEquiv_prod
import Submission.Work.Geo.Prism.Join.exists_barycentric
import Submission.Work.PL.Generic.mem_hullOf
import Submission.Work.PL.Generic.Basic

open Set Metric
open scoped BigOperators

namespace Work.Geo.Prism.Join

noncomputable section
open Classical

private lemma affineMap_sum_apply {n : ℕ} (s : Finset (PL.E n →ᵃ[ℝ] ℝ)) (x : PL.E n) :
    (∑ f ∈ s, f) x = ∑ f ∈ s, f x := by
  let g : (PL.E n →ᵃ[ℝ] ℝ) →+ ℝ :=
    { toFun := fun f => f x, map_zero' := by simp, map_add' := fun f g => by simp }
  exact map_sum g (fun f => f) s

private def unw (q : ℕ) : PL.E q ≃ₗ[ℝ] (Fin q → ℝ) :=
  (EuclideanSpace.equiv (Fin q) ℝ).toLinearEquiv

private def cf (q : ℕ) (i : Fin q) : PL.E q →ᵃ[ℝ] ℝ :=
  ((LinearMap.proj i : (Fin q → ℝ) →ₗ[ℝ] ℝ).comp (unw q).toLinearMap).toAffineMap

private lemma unw_symm_apply (q : ℕ) (v : Fin q → ℝ) : unw q ((unw q).symm v) = v :=
  LinearEquiv.apply_symm_apply _ _

private lemma cf_apply (q : ℕ) (i : Fin q) (w : PL.E q) : cf q i w = unw q w i := by
  simp [cf]

private lemma sum_S_split {n : ℕ} {τ₀ τ₁ S : Finset (PL.E n)} (hS : S = τ₀ ∪ τ₁)
    (hdisj : Disjoint τ₀ τ₁) (f : PL.E n → ℝ) :
    (∑ s : ↥S, f s.1) = (∑ i : ↥τ₀, f i.1) + (∑ j : ↥τ₁, f j.1) := by
  rw [← Finset.sum_subtype S (fun _ => Iff.rfl) f, hS, Finset.sum_union hdisj,
    ← Finset.sum_subtype τ₀ (fun _ => Iff.rfl) f, ← Finset.sum_subtype τ₁ (fun _ => Iff.rfl) f]

lemma finrank_direction {n : ℕ} (S : Finset (PL.E n)) {m : ℕ} (hc : S.card = m + 1)
    (hind : AffineIndependent ℝ (fun v : S => (v : PL.E n))) :
    Module.finrank ℝ (affineSpan ℝ (S : Set (PL.E n))).direction = m := by
  rw [direction_affineSpan]
  have h : (Finset.univ.image (fun v : S => (v : PL.E n)) : Set (PL.E n)) = (S : Set (PL.E n)) := by
    ext x; simp
  rw [← h]
  exact hind.finrank_vectorSpan_image_finset (s := Finset.univ) (n := m)
    (by simpa [Finset.card_univ] using hc)

theorem join_simplex_prism {n q : ℕ} (hq : q + 1 ≤ n) (τ₀ τ₁ : Finset (PL.E n))
    (hne₀ : τ₀.Nonempty) (hne₁ : τ₁.Nonempty) (hdisj : Disjoint τ₀ τ₁)
    (hcard : (τ₀ ∪ τ₁).card = q + 2)
    (hind : AffineIndependent ℝ (fun v : (τ₀ ∪ τ₁ : Finset (PL.E n)) => (v : PL.E n))) :
    ∃ (T : PL.E n ≃ᵃ[ℝ] Work.Geo.Prism.Pr (n - q - 1) q) (F : Set (PL.E q))
      (γ₀ γ₁ : PL.E q → ℝ),
      IsCompact F ∧ Convex ℝ F ∧ Continuous γ₀ ∧ Continuous γ₁ ∧
      Work.Geo.Prism.ConvexPL γ₀ ∧ Work.Geo.Prism.ConcavePL γ₁ ∧
      (∀ z ∈ F, γ₀ z ≤ γ₁ z) ∧ (∀ z ∈ frontier F, γ₀ z = γ₁ z) ∧
      T '' PL.simp (τ₀ ∪ τ₁) = {x | x.1 = 0 ∧ x.2.1 ∈ F ∧ γ₀ x.2.1 ≤ x.2.2 ∧ x.2.2 ≤ γ₁ x.2.1} ∧
      T '' (⋃ w ∈ τ₁, PL.simp ((τ₀ ∪ τ₁).erase w)) =
        {x | x.1 = 0 ∧ x.2.1 ∈ F ∧ x.2.2 = γ₀ x.2.1} ∧
      T '' (⋃ w ∈ τ₀, PL.simp ((τ₀ ∪ τ₁).erase w)) =
        {x | x.1 = 0 ∧ x.2.1 ∈ F ∧ x.2.2 = γ₁ x.2.1} := by
  classical
  have hne₀' : τ₀.Nonempty := hne₀
  obtain ⟨i₀, hi₀⟩ := hne₀'
  have hne₁' : τ₁.Nonempty := hne₁
  obtain ⟨j₀, hj₀⟩ := hne₁'
  set S : Finset (PL.E n) := τ₀ ∪ τ₁ with hSdef
  have hSne : S.Nonempty := ⟨i₀, by rw [hSdef]; exact Finset.mem_union_left τ₁ hi₀⟩
  have hcardS : S.card = q + 2 := by rw [hSdef]; exact hcard
  have hindS : AffineIndependent ℝ (fun v : S => (v : PL.E n)) := by rw [hSdef]; exact hind
  have hmem0 : ∀ w ∈ τ₀, w ∈ S := fun w hw => by rw [hSdef]; exact Finset.mem_union_left τ₁ hw
  have hmem1 : ∀ w ∈ τ₁, w ∈ S := fun w hw => by rw [hSdef]; exact Finset.mem_union_right τ₀ hw
  have hpr : τ₀.card + τ₁.card = q + 2 := by
    rw [← Finset.card_union_of_disjoint hdisj]; exact hcard
  have hp0 : 1 ≤ τ₀.card := Finset.card_pos.mpr hne₀
  have hr0 : 1 ≤ τ₁.card := Finset.card_pos.mpr hne₁
  obtain ⟨lam, hlam_self, hlam_ne, hlam⟩ := exists_barycentric n S hSne hindS
  set D : AffineSubspace ℝ (PL.E n) := affineSpan ℝ (S : Set (PL.E n)) with hDdef
  set W : Submodule ℝ (PL.E n) := D.direction with hWdef
  have hlamD : ∀ x ∈ (D : Set (PL.E n)), (∑ s : ↥S, lam s x) = 1 ∧
      (∑ s : ↥S, (lam s x) • (s : PL.E n)) = x := hlam
  set ιz : Finset (PL.E n) := (τ₀.erase i₀) ∪ (τ₁.erase j₀) with hιzdef
  have hcardιz : ιz.card = q := by
    have hdisj' : Disjoint (τ₀.erase i₀) (τ₁.erase j₀) :=
      hdisj.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
    rw [hιzdef, Finset.card_union_of_disjoint hdisj',
      Finset.card_erase_of_mem hi₀, Finset.card_erase_of_mem hj₀]
    omega
  set ez : ↥ιz ≃ Fin q := Finset.equivFinOfCardEq hcardιz with hezdef
  have hιz0 : ∀ i ∈ τ₀.erase i₀, i ∈ ιz := fun i hi => by rw [hιzdef]; exact Finset.mem_union_left _ hi
  have hιz1 : ∀ j ∈ τ₁.erase j₀, j ∈ ιz := fun j hj => by rw [hιzdef]; exact Finset.mem_union_right _ hj
  set Afun : PL.E n → (PL.E q →ᵃ[ℝ] ℝ) := fun u =>
    if h : u = i₀ then 0 else if h2 : u ∈ τ₀.erase i₀ then cf q (ez ⟨u, hιz0 u h2⟩) else 0
    with hAfundef
  set Bfun : PL.E n → (PL.E q →ᵃ[ℝ] ℝ) := fun u =>
    if h : u = j₀ then 0 else if h2 : u ∈ τ₁.erase j₀ then cf q (ez ⟨u, hιz1 u h2⟩) else 0
    with hBfundef
  set sumA : PL.E q →ᵃ[ℝ] ℝ := ∑ i : ↥τ₀, Afun i.1 with hsumAdef
  set sumB : PL.E q →ᵃ[ℝ] ℝ := ∑ j : ↥τ₁, Bfun j.1 with hsumBdef
  set g0 : ↥τ₁ → (PL.E q →ᵃ[ℝ] ℝ) := fun j => sumB - (τ₁.card : ℝ) • Bfun j.1 with hg0def
  set g1 : ↥τ₀ → (PL.E q →ᵃ[ℝ] ℝ) :=
    fun i => (AffineMap.const ℝ (PL.E q) (1 : ℝ)) - sumA + (τ₀.card : ℝ) • Afun i.1 with hg1def
  set γ₀ : PL.E q → ℝ := fun w => Finset.sup' τ₁.attach hne₁.attach (fun j => g0 j w) with hγ₀def
  set γ₁ : PL.E q → ℝ := fun w => Finset.inf' τ₀.attach hne₀.attach (fun i => g1 i w) with hγ₁def
  set F : Set (PL.E q) := {w | γ₀ w ≤ γ₁ w} with hFdef
  set lamF : PL.E n → (PL.E n →ᵃ[ℝ] ℝ) :=
    fun w => if h : w ∈ S then lam ⟨w, h⟩ else 0 with hlamFdef
  set zc : Fin q → (PL.E n →ᵃ[ℝ] ℝ) := fun k =>
      if h : ((ez.symm k : ↥ιz) : PL.E n) ∈ τ₀ then
        lamF ((ez.symm k : ↥ιz) : PL.E n) - lamF i₀
      else
        lamF ((ez.symm k : ↥ιz) : PL.E n) - lamF j₀ with hzcdef
  set z : PL.E n →ᵃ[ℝ] PL.E q :=
    (unw q).symm.toAffineEquiv.toAffineMap.comp (AffineMap.pi zc) with hzdef
  set tau : PL.E n →ᵃ[ℝ] ℝ := ∑ j : ↥τ₁, lamF j.1 with htaudef
  set Z : PL.E n →ᵃ[ℝ] (PL.E q × ℝ) := z.prod tau with hZdef
  -- evaluation of sums of affine maps
  have eval_sum' : ∀ {ι : Type} [Fintype ι] (f : ι → (PL.E n →ᵃ[ℝ] ℝ)) (x : PL.E n),
      (∑ i : ι, f i) x = ∑ i : ι, f i x := by
    intro ι _ f x
    let hh : (PL.E n →ᵃ[ℝ] ℝ) →+ ℝ :=
      { toFun := fun g => g x, map_zero' := by simp, map_add' := fun g h => by simp }
    exact map_sum hh f Finset.univ
  have eval_sumq : ∀ {ι : Type} [Fintype ι] (f : ι → (PL.E q →ᵃ[ℝ] ℝ)) (w : PL.E q),
      (∑ i : ι, f i) w = ∑ i : ι, f i w := by
    intro ι _ f w
    let hh : (PL.E q →ᵃ[ℝ] ℝ) →+ ℝ :=
      { toFun := fun g => g w, map_zero' := by simp, map_add' := fun g h => by simp }
    exact map_sum hh f Finset.univ
  -- affine combination lemma
  have affineComb' : ∀ {ι : Type} [Fintype ι] (f : PL.E n →ᵃ[ℝ] ℝ) (p : ι → PL.E n) (μ : ι → ℝ),
      (∑ i, μ i) = 1 → f (∑ i, μ i • p i) = ∑ i, μ i * f (p i) := by
    intro ι _ f p μ hμ
    have h1 : (∑ i, μ i • p i) = (Finset.affineCombination ℝ Finset.univ p) μ := by
      rw [Finset.affineCombination_eq_linear_combination Finset.univ p μ (by simpa using hμ)]
    rw [h1, Finset.map_affineCombination Finset.univ p μ (by simpa using hμ) f,
      Finset.affineCombination_eq_linear_combination Finset.univ (f ∘ p) μ (by simpa using hμ)]
    simp
  -- basic lamF facts
  have lamF_of_mem : ∀ w (hw : w ∈ S), lamF w = lam ⟨w, hw⟩ := by
    intro w hw; rw [hlamFdef]; simp only [dif_pos hw]
  have lamF_pos : ∀ w ∈ S, lamF w w = 1 := by
    intro w hw; rw [lamF_of_mem w hw]; exact hlam_self ⟨w, hw⟩
  have lamF_neq : ∀ w ∈ S, ∀ w' ∈ S, w ≠ w' → lamF w w' = 0 := by
    intro w hw w' hw' hne; rw [lamF_of_mem w hw]
    exact hlam_ne ⟨w,hw⟩ ⟨w',hw'⟩ (fun h => hne (congrArg Subtype.val h))
  have lamF_sum : ∀ x ∈ (D:Set (PL.E n)), (∑ w ∈ S, lamF w x) = 1 := by
    intro x hx
    have h2 : (∑ w ∈ S, lamF w x) = ∑ s : ↥S, lam s x := by
      rw [Finset.sum_subtype S (fun _ => Iff.rfl) (fun w => lamF w x)]
      apply Finset.sum_congr rfl; intro a _
      rw [lamF_of_mem a.1 a.2]
    rw [h2]; exact (hlamD x hx).1
  have lamF_comb : ∀ x ∈ (D:Set (PL.E n)), (∑ w ∈ S, (lamF w x) • w) = x := by
    intro x hx
    have h2 : (∑ w ∈ S, (lamF w x) • w) = ∑ s : ↥S, (lam s x) • (s : PL.E n) := by
      rw [Finset.sum_subtype S (fun _ => Iff.rfl) (fun w => (lamF w x) • w)]
      apply Finset.sum_congr rfl; intro a _
      rw [lamF_of_mem a.1 a.2]
    rw [h2]; exact (hlamD x hx).2
  have cf_z : ∀ (x : PL.E n) (k : Fin q), cf q k (z x) = zc k x := by
    intro x k
    have hz : z x = (unw q).symm ((AffineMap.pi zc) x) := by rw [hzdef]; rfl
    rw [hz, cf_apply, unw_symm_apply, AffineMap.pi_apply]
  have zc_A : ∀ (i : PL.E n) (hi : i ∈ τ₀.erase i₀) (x : PL.E n),
      zc (ez ⟨i, hιz0 i hi⟩) x = lamF i x - lamF i₀ x := by
    intro i hi x
    have hmem : (((ez.symm (ez ⟨i, hιz0 i hi⟩) : ↥ιz)) : PL.E n) ∈ τ₀ := by
      rw [Equiv.symm_apply_apply]; exact Finset.mem_of_mem_erase hi
    have hval : (((ez.symm (ez ⟨i, hιz0 i hi⟩) : ↥ιz)) : PL.E n) = i := by
      rw [Equiv.symm_apply_apply]
    simp only [hzcdef, dif_pos hmem, hval]
    simp
  have zc_B : ∀ (j : PL.E n) (hj : j ∈ τ₁.erase j₀) (x : PL.E n),
      zc (ez ⟨j, hιz1 j hj⟩) x = lamF j x - lamF j₀ x := by
    intro j hj x
    have hmem : (((ez.symm (ez ⟨j, hιz1 j hj⟩) : ↥ιz)) : PL.E n) ∈ τ₁ := by
      rw [Equiv.symm_apply_apply]; exact Finset.mem_of_mem_erase hj
    have hnot : ¬ (((ez.symm (ez ⟨j, hιz1 j hj⟩) : ↥ιz)) : PL.E n) ∈ τ₀ :=
      fun hc => (Finset.disjoint_left.mp hdisj.symm) hmem hc
    have hval : (((ez.symm (ez ⟨j, hιz1 j hj⟩) : ↥ιz)) : PL.E n) = j := by
      rw [Equiv.symm_apply_apply]
    simp only [hzcdef, dif_neg hnot, hval]
    simp
  -- Afun/Bfun values
  have Afun_i0 : Afun i₀ = 0 := by rw [hAfundef]; simp
  have Bfun_j0 : Bfun j₀ = 0 := by rw [hBfundef]; simp
  have Afun_notMem : ∀ u, u ∉ τ₀ → u ≠ i₀ → Afun u = 0 := by
    intro u hu hne; rw [hAfundef]; simp only [dif_neg hne, dif_neg (fun h2 => hu (Finset.mem_of_mem_erase h2))]
  have Bfun_notMem : ∀ u, u ∉ τ₁ → u ≠ j₀ → Bfun u = 0 := by
    intro u hu hne; rw [hBfundef]; simp only [dif_neg hne, dif_neg (fun h2 => hu (Finset.mem_of_mem_erase h2))]
  have Afun_of_mem : ∀ (u : PL.E n) (hu : u ∈ τ₀) (hne : u ≠ i₀),
      Afun u = cf q (ez ⟨u, hιz0 u (Finset.mem_erase.mpr ⟨hne, hu⟩)⟩) := by
    intro u hu hne; rw [hAfundef]; simp only [dif_neg hne, dif_pos (Finset.mem_erase.mpr ⟨hne, hu⟩)]
  have Bfun_of_mem : ∀ (u : PL.E n) (hu : u ∈ τ₁) (hne : u ≠ j₀),
      Bfun u = cf q (ez ⟨u, hιz1 u (Finset.mem_erase.mpr ⟨hne, hu⟩)⟩) := by
    intro u hu hne; rw [hBfundef]; simp only [dif_neg hne, dif_pos (Finset.mem_erase.mpr ⟨hne, hu⟩)]
  have Afun_z : ∀ (u : PL.E n) (hu : u ∈ τ₀) (x : PL.E n), Afun u (z x) = lamF u x - lamF i₀ x := by
    intro u hu x
    by_cases h : u = i₀
    · rw [h, Afun_i0]; simp
    · rw [Afun_of_mem u hu h]
      have hi : u ∈ τ₀.erase i₀ := Finset.mem_erase.mpr ⟨h, hu⟩
      rw [cf_z x (ez ⟨u, hιz0 u hi⟩), zc_A u hi x]
  have Bfun_z : ∀ (u : PL.E n) (hu : u ∈ τ₁) (x : PL.E n), Bfun u (z x) = lamF u x - lamF j₀ x := by
    intro u hu x
    by_cases h : u = j₀
    · rw [h, Bfun_j0]; simp
    · rw [Bfun_of_mem u hu h]
      have hj : u ∈ τ₁.erase j₀ := Finset.mem_erase.mpr ⟨h, hu⟩
      rw [cf_z x (ez ⟨u, hιz1 u hj⟩), zc_B u hj x]
  have sumA_apply : ∀ w, sumA w = ∑ i : ↥τ₀, Afun i.1 w := by
    intro w; rw [hsumAdef]; exact eval_sumq (f := fun i : ↥τ₀ => Afun i.1) w
  have sumB_apply : ∀ w, sumB w = ∑ j : ↥τ₁, Bfun j.1 w := by
    intro w; rw [hsumBdef]; exact eval_sumq (f := fun j : ↥τ₁ => Bfun j.1) w
  have tau_apply : ∀ x, tau x = ∑ j : ↥τ₁, lamF j.1 x := by
    intro x; rw [htaudef]; exact eval_sum' (ι := ↥τ₁) (fun j => lamF j.1) x
  have sum_tau0 : ∀ x ∈ (D:Set (PL.E n)), (∑ i : ↥τ₀, lamF i.1 x) = 1 - tau x := by
    intro x hx
    have h1 := lamF_sum x hx
    rw [hSdef, Finset.sum_union hdisj] at h1
    rw [Finset.sum_subtype τ₀ (fun _ => Iff.rfl) (fun w => lamF w x),
        Finset.sum_subtype τ₁ (fun _ => Iff.rfl) (fun w => lamF w x)] at h1
    have h2 : tau x = ∑ j : ↥τ₁, lamF j.1 x := tau_apply x
    linarith
  have sum_tau1 : ∀ x ∈ (D:Set (PL.E n)), (∑ j : ↥τ₁, lamF j.1 x) = tau x := by
    intro x hx; rw [tau_apply x]
  have sumA_z : ∀ x ∈ (D:Set (PL.E n)), sumA (z x) = 1 - tau x - (τ₀.card : ℝ) * lamF i₀ x := by
    intro x hx
    rw [sumA_apply]
    rw [Finset.sum_congr rfl (fun i _ => Afun_z i.1 i.2 x)]
    rw [Finset.sum_sub_distrib]
    have h2 : (∑ _i : ↥τ₀, lamF i₀ x) = (τ₀.card : ℝ) * lamF i₀ x := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe]
    rw [h2, sum_tau0 x hx]
  have sumB_z : ∀ x ∈ (D:Set (PL.E n)), sumB (z x) = tau x - (τ₁.card : ℝ) * lamF j₀ x := by
    intro x hx
    rw [sumB_apply]
    rw [Finset.sum_congr rfl (fun j _ => Bfun_z j.1 j.2 x)]
    rw [Finset.sum_sub_distrib]
    have h2 : (∑ _j : ↥τ₁, lamF j₀ x) = (τ₁.card : ℝ) * lamF j₀ x := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe]
    rw [h2, sum_tau1 x hx]
  have lamF_i0 : ∀ x ∈ (D:Set (PL.E n)),
      (τ₀.card : ℝ) * lamF i₀ x = 1 - tau x - sumA (z x) := by
    intro x hx; rw [sumA_z x hx]; ring
  have lamF_j0 : ∀ x ∈ (D:Set (PL.E n)),
      (τ₁.card : ℝ) * lamF j₀ x = tau x - sumB (z x) := by
    intro x hx; rw [sumB_z x hx]; ring
  have hpR : (τ₀.card : ℝ) ≠ 0 := by
    have : (0:ℝ) < τ₀.card := by exact_mod_cast hp0
    exact ne_of_gt this
  have hrR : (τ₁.card : ℝ) ≠ 0 := by
    have : (0:ℝ) < τ₁.card := by exact_mod_cast hr0
    exact ne_of_gt this
  have lamF_i0_div : ∀ x ∈ (D:Set (PL.E n)), lamF i₀ x = (1 - tau x - sumA (z x)) / (τ₀.card : ℝ) := by
    intro x hx; rw [← lamF_i0 x hx]; field_simp
  have lamF_j0_div : ∀ x ∈ (D:Set (PL.E n)), lamF j₀ x = (tau x - sumB (z x)) / (τ₁.card : ℝ) := by
    intro x hx; rw [← lamF_j0 x hx]; field_simp
  -- the inverse family mu
  set mu : ↥S → (PL.E q × ℝ → ℝ) := fun s wt =>
    if hs : s.1 ∈ τ₀ then
      Afun s.1 wt.1 + (1 - wt.2 - sumA wt.1) / (τ₀.card : ℝ)
    else
      Bfun s.1 wt.1 + (wt.2 - sumB wt.1) / (τ₁.card : ℝ) with hmudef
  set muF : PL.E n → (PL.E q × ℝ → ℝ) :=
    fun w => if h : w ∈ S then mu ⟨w, h⟩ else 0 with hmuFdef
  have muF_of_mem : ∀ w (hw : w ∈ S), muF w = mu ⟨w, hw⟩ := by
    intro w hw; rw [hmuFdef]; simp only [dif_pos hw]
  have muF_of_mem' : ∀ (w : PL.E n) (hw : w ∈ S) (p' : PL.E q × ℝ),
      muF w p' = mu ⟨w, hw⟩ p' := fun w hw p' => congrFun (muF_of_mem w hw) p'
  have mu_tau0 : ∀ (w : PL.E q) (t : ℝ),
      (∑ i : ↥τ₀, mu ⟨i.1, hmem0 i.1 i.2⟩ (w,t)) = 1 - t := by
    intro w t
    have hstep : ∀ i : ↥τ₀, mu ⟨i.1, hmem0 i.1 i.2⟩ (w,t)
        = Afun i.1 w + (1 - t - sumA w) / (τ₀.card : ℝ) := by
      intro i
      rw [hmudef]
      simp only [dif_pos i.2]
    rw [Finset.sum_congr rfl (fun i _ => hstep i)]
    rw [Finset.sum_add_distrib, ← sumA_apply w]
    have hcard : (∑ _i : ↥τ₀, (1 - t - sumA w) / (τ₀.card : ℝ))
        = (τ₀.card : ℝ) * ((1 - t - sumA w) / (τ₀.card : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe]
    rw [hcard]
    field_simp
    ring
  have mu_tau1 : ∀ (w : PL.E q) (t : ℝ),
      (∑ j : ↥τ₁, mu ⟨j.1, hmem1 j.1 j.2⟩ (w,t)) = t := by
    intro w t
    have hstep : ∀ j : ↥τ₁, mu ⟨j.1, hmem1 j.1 j.2⟩ (w,t)
        = Bfun j.1 w + (t - sumB w) / (τ₁.card : ℝ) := by
      intro j
      have hnot : ¬ (j.1 ∈ τ₀) := fun hc => (Finset.disjoint_left.mp hdisj) hc j.2
      rw [hmudef]
      simp only [dif_neg hnot]
    rw [Finset.sum_congr rfl (fun j _ => hstep j)]
    rw [Finset.sum_add_distrib, ← sumB_apply w]
    have hcard : (∑ _j : ↥τ₁, (t - sumB w) / (τ₁.card : ℝ))
        = (τ₁.card : ℝ) * ((t - sumB w) / (τ₁.card : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe]
    rw [hcard]
    field_simp
    ring
  have mu_sum : ∀ (w : PL.E q) (t : ℝ), (∑ s : ↥S, mu s (w,t)) = 1 := by
    intro w t
    rw [Finset.sum_congr rfl (fun s _ => by rw [← muF_of_mem s.1 s.2])]
    rw [sum_S_split hSdef hdisj (fun w' => muF w' (w,t))]
    rw [show (∑ i : ↥τ₀, muF i.1 (w,t)) = ∑ i : ↥τ₀, mu ⟨i.1, hmem0 i.1 i.2⟩ (w,t) from
      Finset.sum_congr rfl (fun i _ => by rw [muF_of_mem i.1 (hmem0 i.1 i.2)])]
    rw [show (∑ j : ↥τ₁, muF j.1 (w,t)) = ∑ j : ↥τ₁, mu ⟨j.1, hmem1 j.1 j.2⟩ (w,t) from
      Finset.sum_congr rfl (fun j _ => by rw [muF_of_mem j.1 (hmem1 j.1 j.2)])]
    rw [mu_tau0 w t, mu_tau1 w t]
    ring
  -- x fun
  set xfun : PL.E q → ℝ → PL.E n := fun w t => ∑ s : ↥S, mu s (w,t) • (s : PL.E n) with hxfundef
  have lamF_xfun : ∀ (w : PL.E q) (t : ℝ) (s' : ↥S), lamF s'.1 (xfun w t) = mu s' (w,t) := by
    intro w t s'
    have h1 : lamF s'.1 (xfun w t)
        = ∑ s : ↥S, mu s (w,t) * lamF s'.1 (s : PL.E n) := by
      rw [hxfundef]
      exact affineComb' (lamF s'.1) (fun s : ↥S => (s : PL.E n)) (fun s => mu s (w,t)) (mu_sum w t)
    rw [h1, Finset.sum_eq_single s']
    · rw [lamF_pos s'.1 s'.2, mul_one]
    · intro b _ hb
      rw [lamF_neq s'.1 s'.2 b.1 b.2 (fun h => hb (Subtype.ext h.symm)), mul_zero]
    · intro hb; exact absurd (Finset.mem_univ s') hb
  have xfun_mem : ∀ (w : PL.E q) (t : ℝ), xfun w t ∈ (D:Set (PL.E n)) := by
    intro w t
    have h1 : xfun w t
        = (Finset.affineCombination ℝ Finset.univ (fun s : ↥S => (s : PL.E n))) (fun s => mu s (w,t)) := by
      rw [hxfundef, Finset.affineCombination_eq_linear_combination Finset.univ _ _ (mu_sum w t)]
    rw [h1]
    have hm := affineCombination_mem_affineSpan (s := (Finset.univ : Finset ↥S)) (w := fun s => mu s (w,t))
      (by simpa using mu_sum w t) (fun s : ↥S => (s : PL.E n))
    simpa [hDdef, Subtype.range_coe] using hm
  have tau_xfun : ∀ w t, tau (xfun w t) = t := by
    intro w t
    rw [tau_apply]
    rw [show (∑ j : ↥τ₁, lamF j.1 (xfun w t))
        = ∑ j : ↥τ₁, mu ⟨j.1, hmem1 j.1 j.2⟩ (w,t) from
      Finset.sum_congr rfl (fun j _ => lamF_xfun w t ⟨j.1, hmem1 j.1 j.2⟩)]
    exact mu_tau1 w t
  have zc_apply : ∀ (k : Fin q) (x : PL.E n),
      zc k x = (if ((ez.symm k : ↥ιz) : PL.E n) ∈ τ₀
        then lamF ((ez.symm k : ↥ιz) : PL.E n) x - lamF i₀ x
        else lamF ((ez.symm k : ↥ιz) : PL.E n) x - lamF j₀ x) := by
    intro k x
    simp only [hzcdef]
    split_ifs with hk
    · simp
    · simp
  have hmemS : ∀ x ∈ ιz, x ∈ S := by
    intro x hx
    rw [hιzdef] at hx
    rcases Finset.mem_union.mp hx with h | h
    · exact hmem0 x (Finset.mem_of_mem_erase h)
    · exact hmem1 x (Finset.mem_of_mem_erase h)
  have uk_ne_i0 : ∀ k : Fin q, ((ez.symm k : ↥ιz) : PL.E n) ≠ i₀ := by
    intro k h
    have h1 : i₀ ∈ ιz := h ▸ (ez.symm k).2
    rw [hιzdef] at h1
    rcases Finset.mem_union.mp h1 with h2 | h2
    · exact (Finset.mem_erase.mp h2).1 rfl
    · exact (Finset.disjoint_left.mp hdisj) hi₀ (Finset.mem_of_mem_erase h2)
  have uk_ne_j0 : ∀ k : Fin q, ((ez.symm k : ↥ιz) : PL.E n) ≠ j₀ := by
    intro k h
    have h1 : j₀ ∈ ιz := h ▸ (ez.symm k).2
    rw [hιzdef] at h1
    rcases Finset.mem_union.mp h1 with h2 | h2
    · exact (Finset.disjoint_left.mp hdisj) (Finset.mem_of_mem_erase h2) hj₀
    · exact (Finset.mem_erase.mp h2).1 rfl
  have Afun_uk : ∀ k : Fin q, ((ez.symm k : ↥ιz) : PL.E n) ∈ τ₀ →
      Afun ((ez.symm k : ↥ιz) : PL.E n) = cf q k := by
    intro k hk
    rw [Afun_of_mem _ hk (uk_ne_i0 k)]
    rw [show (⟨((ez.symm k : ↥ιz) : PL.E n),
        hιz0 _ (Finset.mem_erase.mpr ⟨uk_ne_i0 k, hk⟩)⟩ : ↥ιz) = ez.symm k from Subtype.ext rfl,
      Equiv.apply_symm_apply]
  have Bfun_uk : ∀ k : Fin q, ((ez.symm k : ↥ιz) : PL.E n) ∈ τ₁ →
      Bfun ((ez.symm k : ↥ιz) : PL.E n) = cf q k := by
    intro k hk
    rw [Bfun_of_mem _ hk (uk_ne_j0 k)]
    rw [show (⟨((ez.symm k : ↥ιz) : PL.E n),
        hιz1 _ (Finset.mem_erase.mpr ⟨uk_ne_j0 k, hk⟩)⟩ : ↥ιz) = ez.symm k from Subtype.ext rfl,
      Equiv.apply_symm_apply]
  have z_xfun : ∀ w t, z (xfun w t) = w := by
    intro w t
    apply (unw q).injective
    funext k
    rw [← cf_apply q k (z (xfun w t)), cf_z, zc_apply]
    rw [show unw q w k = cf q k w from (cf_apply q k w).symm]
    by_cases hk : ((ez.symm k : ↥ιz) : PL.E n) ∈ τ₀
    · rw [if_pos hk]
      rw [lamF_xfun w t ⟨_, hmemS _ (ez.symm k).2⟩, lamF_xfun w t ⟨i₀, hmem0 i₀ hi₀⟩]
      rw [hmudef]; simp only [dif_pos hk, dif_pos hi₀, Afun_i0, Pi.sub_apply]
      rw [Afun_uk k hk]
      simp
    · rw [if_neg hk]
      have hkT : ((ez.symm k : ↥ιz) : PL.E n) ∈ τ₁ := by
        have hh : ((ez.symm k : ↥ιz) : PL.E n) ∈ (τ₀.erase i₀) ∪ (τ₁.erase j₀) := (ez.symm k).2
        rcases Finset.mem_union.mp hh with h | h
        · exact absurd (Finset.mem_of_mem_erase h) hk
        · exact Finset.mem_of_mem_erase h
      rw [lamF_xfun w t ⟨_, hmemS _ (ez.symm k).2⟩, lamF_xfun w t ⟨j₀, hmem1 j₀ hj₀⟩]
      rw [hmudef]
      simp only [dif_neg hk, dif_neg (fun hc => (Finset.disjoint_left.mp hdisj) hc hj₀), Bfun_j0, Pi.sub_apply]
      rw [Bfun_uk k hkT]
      simp
  -- Fact R
  have FactR : ∀ x ∈ (D:Set (PL.E n)), ∀ (s : ↥S), lamF s.1 x = mu s (z x, tau x) := by
    intro x hx s
    by_cases hs : s.1 ∈ τ₀
    · rw [hmudef]; simp only [dif_pos hs]
      rw [Afun_z s.1 hs x, lamF_i0_div x hx]
      ring
    · have hs1 : s.1 ∈ τ₁ := by
        have hh : s.1 ∈ τ₀ ∪ τ₁ := hSdef ▸ s.2
        rcases Finset.mem_union.mp hh with h0 | h1
        · exact absurd h0 hs
        · exact h1
      rw [hmudef]; simp only [dif_neg hs]
      rw [Bfun_z s.1 hs1 x, lamF_j0_div x hx]
      ring
  -- ============ (a) the affine equivalence T ============
  have inj_on : ∀ x ∈ (D:Set (PL.E n)), ∀ y ∈ (D:Set (PL.E n)),
      z x = z y → tau x = tau y → x = y := by
    intro x hx y hy hz ht
    rw [← lamF_comb x hx, ← lamF_comb y hy]
    apply Finset.sum_congr rfl
    intro s hs
    rw [FactR x hx ⟨s, hs⟩, FactR y hy ⟨s, hs⟩, hz, ht]
  have hWfin : Module.finrank ℝ W = q + 1 := finrank_direction S hcardS hindS
  have hfinEn : Module.finrank ℝ (PL.E n) = n := by rw [finrank_euclideanSpace]; simp
  have hqdim : Module.finrank ℝ (PL.E n ⧸ W) = n - (q + 1) := by
    have h := Submodule.finrank_quotient_add_finrank (R := ℝ) W
    rw [hfinEn, hWfin] at h
    omega
  have hdimEq : Module.finrank ℝ (PL.E n ⧸ W) = Module.finrank ℝ (PL.E (n - q - 1)) := by
    rw [hqdim, finrank_euclideanSpace]; simp; omega
  let ee : (PL.E n ⧸ W) ≃ₗ[ℝ] PL.E (n - q - 1) := LinearEquiv.ofFinrankEq (R := ℝ) (PL.E n ⧸ W) (PL.E (n - q - 1)) hdimEq
  let π : PL.E n →ₗ[ℝ] PL.E (n - q - 1) := ee.toLinearMap.comp W.mkQ
  have hπ : π.ker = W := by
    have h1 : π.ker = (W.mkQ).ker := by
      ext x
      rw [LinearMap.mem_ker, LinearMap.mem_ker]
      constructor
      · intro hx
        exact ee.injective (by simpa [π] using hx)
      · intro hx
        change ee (W.mkQ x) = 0
        rw [hx, map_zero]
    rw [h1, Submodule.ker_mkQ]
  have hi₀D : i₀ ∈ (D:Set (PL.E n)) := mem_affineSpan ℝ (by rw [hSdef]; exact Finset.mem_union_left τ₁ hi₀)
  have hZD : ∀ v ∈ W, Z.linear v = 0 → v = 0 := by
    intro v hv h0
    have h1 : Z (v +ᵥ i₀) = Z i₀ := by rw [AffineMap.map_vadd, h0]; simp
    have hprod : z (v +ᵥ i₀) = z i₀ ∧ tau (v +ᵥ i₀) = tau i₀ := by
      simpa [hZdef, AffineMap.prod_apply, Prod.mk.injEq] using h1
    have hmem : v +ᵥ i₀ ∈ (D:Set (PL.E n)) := AffineSubspace.vadd_mem_of_mem_direction hv hi₀D
    have h2 := inj_on (v +ᵥ i₀) hmem i₀ hi₀D hprod.1 hprod.2
    have h3 : v + i₀ = i₀ := by simpa [vadd_eq_add] using h2
    have : v = 0 := by
      have := congrArg (· - i₀) h3
      simpa using this
    exact this
  have hFdim : Module.finrank ℝ (PL.E q × ℝ) = Module.finrank ℝ W := by
    rw [Module.finrank_prod, hWfin, finrank_euclideanSpace]; simp
  have hae : (n - q - 1) + Module.finrank ℝ W = n := by rw [hWfin]; omega
  obtain ⟨T, hT⟩ := exists_affineEquiv_prod W π hπ hae Z i₀ hZD hFdim
  have hTD : ∀ x ∈ (D:Set (PL.E n)), T x = (0, z x, tau x) := by
    intro x hx
    have hker : x -ᵥ i₀ ∈ π.ker := by
      rw [hπ]; exact AffineSubspace.vsub_mem_direction hx hi₀D
    have hzero : π (x -ᵥ i₀) = 0 := LinearMap.mem_ker.mp hker
    rw [hT x, hzero]
    rfl
  -- ============ (b) F and the PL functions ============
  have affineComb : ∀ (f : PL.E n →ᵃ[ℝ] ℝ) (s : Finset (PL.E n)) (μ : PL.E n → ℝ),
      (∑ v ∈ s, μ v) = 1 → f (∑ v ∈ s, μ v • v) = ∑ v ∈ s, μ v * f v := by
    intro f s μ hμ
    have h1 : (∑ v ∈ s, μ v • v) = (Finset.affineCombination ℝ s (id : PL.E n → PL.E n)) μ :=
      (Finset.affineCombination_eq_linear_combination s id μ hμ).symm
    rw [h1, Finset.map_affineCombination s id μ hμ f,
      Finset.affineCombination_eq_linear_combination s (f ∘ id) μ hμ]
    simp
  have mem_simp_gen : ∀ (s : Finset (PL.E n)) (x : PL.E n), x ∈ PL.simp s ↔
      ∃ w : PL.E n → ℝ, (∀ v ∈ s, 0 ≤ w v) ∧ (∑ v ∈ s, w v) = 1 ∧ (∑ v ∈ s, w v • v) = x := by
    intro s x
    have h := Work.PL.Generic.mem_hullOf (id : PL.E n → PL.E n) s x
    rw [Work.PL.Generic.hullOf_eq_simp, Finset.image_id] at h
    exact h
  have lamF_nonneg : ∀ x ∈ PL.simp S, ∀ s ∈ S, 0 ≤ lamF s x := by
    intro x hx s hs
    obtain ⟨w, hw0, hw1, hwx⟩ := (mem_simp_gen S x).mp hx
    rw [← hwx, affineComb (lamF s) S w hw1]
    have hsum : (∑ v ∈ S, w v * lamF s v) = w s := by
      rw [Finset.sum_eq_single s]
      · rw [lamF_pos s hs, mul_one]
      · intro b hb hbs
        rw [lamF_neq s hs b hb (fun h => hbs h.symm), mul_zero]
      · intro hs'; exact absurd hs hs'
    rw [hsum]; exact hw0 s hs
  have g0_eval : ∀ (j : ↥τ₁) (x : PL.E n), x ∈ (D:Set (PL.E n)) →
      g0 j (z x) = tau x - (τ₁.card : ℝ) * lamF j.1 x := by
    intro j x hx
    rw [show g0 j (z x) = sumB (z x) - (τ₁.card : ℝ) * Bfun j.1 (z x) from by
      simp only [hg0def, AffineMap.coe_sub, AffineMap.coe_smul, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul], sumB_z x hx, Bfun_z j.1 j.2 x]
    ring
  have g1_eval : ∀ (i : ↥τ₀) (x : PL.E n), x ∈ (D:Set (PL.E n)) →
      g1 i (z x) = tau x + (τ₀.card : ℝ) * lamF i.1 x := by
    intro i x hx
    rw [show g1 i (z x) = 1 - sumA (z x) + (τ₀.card : ℝ) * Afun i.1 (z x) from by
      simp only [hg1def, AffineMap.coe_sub, AffineMap.coe_add, AffineMap.coe_smul, AffineMap.const_apply,
        Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul], sumA_z x hx, Afun_z i.1 i.2 x]
    have h := lamF_i0 x hx
    ring
  have g0_le : ∀ x ∈ PL.simp S, γ₀ (z x) ≤ tau x := by
    intro x hx
    have hxD : x ∈ (D:Set (PL.E n)) := PL.simp_subset_affineSpan S hx
    rw [hγ₀def]
    apply Finset.sup'_le
    intro j _
    rw [g0_eval j x hxD]
    have hr : (0:ℝ) ≤ (τ₁.card : ℝ) := by exact_mod_cast Nat.zero_le τ₁.card
    exact sub_le_self _ (mul_nonneg hr (lamF_nonneg x hx j.1 (hmem1 j.1 j.2)))
  have g1_ge : ∀ x ∈ PL.simp S, tau x ≤ γ₁ (z x) := by
    intro x hx
    have hxD : x ∈ (D:Set (PL.E n)) := PL.simp_subset_affineSpan S hx
    rw [hγ₁def]
    apply Finset.le_inf'
    intro i _
    rw [g1_eval i x hxD]
    have hr : (0:ℝ) ≤ (τ₀.card : ℝ) := by exact_mod_cast Nat.zero_le τ₀.card
    exact le_add_of_nonneg_right (mul_nonneg hr (lamF_nonneg x hx i.1 (hmem0 i.1 i.2)))
  -- the region
  have mu_nonneg : ∀ (w : PL.E q) (t : ℝ), w ∈ F → γ₀ w ≤ t → t ≤ γ₁ w →
      ∀ s : ↥S, 0 ≤ mu s (w, t) := by
    intro w t hw hle hge s
    by_cases hs : s.1 ∈ τ₀
    · rw [hmudef]; simp only [dif_pos hs]
      have hmem : (⟨s.1, hs⟩ : ↥τ₀) ∈ τ₀.attach := by rw [Finset.attach_eq_univ]; exact Finset.mem_univ _
      have h1 : t ≤ g1 ⟨s.1, hs⟩ w :=
        le_trans hge (Finset.inf'_le (fun i : ↥τ₀ => g1 i w) hmem)
      have h3 : (0:ℝ) < τ₀.card := by exact_mod_cast hp0
      have heq : Afun s.1 w + (1 - t - sumA w) / (τ₀.card : ℝ)
          = (g1 ⟨s.1, hs⟩ w - t) / (τ₀.card : ℝ) := by
        rw [show g1 ⟨s.1, hs⟩ w = 1 - sumA w + (τ₀.card : ℝ) * Afun s.1 w from by
          simp only [hg1def, AffineMap.coe_sub, AffineMap.coe_add, AffineMap.coe_smul, AffineMap.const_apply,
            Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]]
        field_simp
        ring
      rw [heq]; exact div_nonneg (sub_nonneg.mpr h1) (le_of_lt h3)
    · have hs1 : s.1 ∈ τ₁ := by
        have hh : s.1 ∈ τ₀ ∪ τ₁ := hSdef ▸ s.2
        rcases Finset.mem_union.mp hh with h0 | h1
        · exact absurd h0 hs
        · exact h1
      rw [hmudef]; simp only [dif_neg hs]
      have hmem : (⟨s.1, hs1⟩ : ↥τ₁) ∈ τ₁.attach := by rw [Finset.attach_eq_univ]; exact Finset.mem_univ _
      have h1 : g0 ⟨s.1, hs1⟩ w ≤ t :=
        le_trans (Finset.le_sup' (fun j : ↥τ₁ => g0 j w) hmem) hle
      have h3 : (0:ℝ) < τ₁.card := by exact_mod_cast hr0
      have heq : Bfun s.1 w + (t - sumB w) / (τ₁.card : ℝ)
          = (t - g0 ⟨s.1, hs1⟩ w) / (τ₁.card : ℝ) := by
        rw [show g0 ⟨s.1, hs1⟩ w = sumB w - (τ₁.card : ℝ) * Bfun s.1 w from by
          simp only [hg0def, AffineMap.coe_sub, AffineMap.coe_smul, Pi.sub_apply, Pi.smul_apply,
            smul_eq_mul]]
        field_simp
        ring
      rw [heq]; exact div_nonneg (sub_nonneg.mpr h1) (le_of_lt h3)
  -- H4
  have h4 : T '' PL.simp S = {y : PL.E (n - q - 1) × (PL.E q × ℝ) |
      y.1 = 0 ∧ y.2.1 ∈ F ∧ γ₀ y.2.1 ≤ y.2.2 ∧ y.2.2 ≤ γ₁ y.2.1} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxD : x ∈ (D:Set (PL.E n)) := PL.simp_subset_affineSpan S hx
      rw [hTD x hxD]
      exact ⟨rfl, le_trans (g0_le x hx) (g1_ge x hx), g0_le x hx, g1_ge x hx⟩
    · rintro ⟨h1, h2, h3, h4'⟩
      refine ⟨xfun y.2.1 y.2.2, ?_, ?_⟩
      · refine (mem_simp_gen S (xfun y.2.1 y.2.2)).mpr
          ⟨fun v => muF v (y.2.1, y.2.2), ?_, ?_, ?_⟩
        · intro v hv
          show 0 ≤ muF v (y.2.1, y.2.2)
          rw [muF_of_mem' v hv]
          exact mu_nonneg y.2.1 y.2.2 h2 h3 h4' ⟨v, hv⟩
        · have hsum : (∑ v ∈ S, muF v (y.2.1, y.2.2)) = ∑ v : ↥S, mu v (y.2.1, y.2.2) := by
            rw [Finset.sum_subtype S (fun _ => Iff.rfl) (fun v => muF v (y.2.1, y.2.2))]
            exact Finset.sum_congr rfl (fun v _ => muF_of_mem' v.1 v.2 (y.2.1, y.2.2))
          rw [hsum]; exact mu_sum y.2.1 y.2.2
        · have hsum : (∑ v ∈ S, muF v (y.2.1, y.2.2) • v)
              = ∑ v : ↥S, mu v (y.2.1, y.2.2) • (v : PL.E n) := by
            rw [Finset.sum_subtype S (fun _ => Iff.rfl) (fun v => muF v (y.2.1, y.2.2) • v)]
            exact Finset.sum_congr rfl (fun v _ => by rw [muF_of_mem' v.1 v.2 (y.2.1, y.2.2)])
          rw [hsum, hxfundef]
      · have hxd : xfun y.2.1 y.2.2 ∈ (D:Set (PL.E n)) := xfun_mem _ _
        rw [hTD _ hxd, z_xfun, tau_xfun]
        exact Prod.ext h1.symm (Prod.ext rfl rfl)
  -- F is the image of the simplex
  have hF_eq : F = z '' PL.simp S := by
    ext w
    constructor
    · intro hw
      have hy : ((0 : PL.E (n - q - 1)), w, γ₀ w) ∈ {y : PL.E (n - q - 1) × (PL.E q × ℝ) |
          y.1 = 0 ∧ y.2.1 ∈ F ∧ γ₀ y.2.1 ≤ y.2.2 ∧ y.2.2 ≤ γ₁ y.2.1} :=
        ⟨rfl, hw, le_refl _, hw⟩
      rw [← h4] at hy
      obtain ⟨x, hx, hTx⟩ := hy
      refine ⟨x, hx, ?_⟩
      have hEq := hTx
      rw [hTD x (PL.simp_subset_affineSpan S hx)] at hEq
      have h21 : (0, z x, tau x).2.1 = (0, w, γ₀ w).2.1 := congrArg (fun p => p.2.1) hEq
      simpa using h21
    · rintro ⟨x, hx, rfl⟩
      have hy : T x ∈ {y : PL.E (n - q - 1) × (PL.E q × ℝ) |
          y.1 = 0 ∧ y.2.1 ∈ F ∧ γ₀ y.2.1 ≤ y.2.2 ∧ y.2.2 ≤ γ₁ y.2.1} := by
        rw [← h4]; exact ⟨x, hx, rfl⟩
      rw [hTD x (PL.simp_subset_affineSpan S hx)] at hy
      exact hy.2.1
  have hFcompact : IsCompact F := by
    rw [hF_eq]
    exact (PL.isCompact_simp S).image (f := z) (AffineMap.continuous_of_finiteDimensional z)
  have hFconvex : Convex ℝ F := by
    rw [hF_eq, PL.simp, AffineMap.image_convexHull]
    exact convex_convexHull ℝ _
  have hγ₀cont : Continuous γ₀ := by
    rw [hγ₀def]
    exact Continuous.finset_sup'_apply hne₁.attach
      (fun i _ => AffineMap.continuous_of_finiteDimensional (g0 i))
  have hγ₁cont : Continuous γ₁ := by
    rw [hγ₁def]
    exact Continuous.finset_inf'_apply hne₀.attach
      (fun i _ => AffineMap.continuous_of_finiteDimensional (g1 i))
  have hγ₀PL : Work.Geo.Prism.ConvexPL γ₀ := by
    refine ⟨τ₁.attach.image g0, hne₁.attach.image g0, fun w => ?_⟩
    rw [hγ₀def]
    exact (Finset.sup'_image (hne₁.attach.image g0) (fun f => f w)).symm
  have hγ₁PL : Work.Geo.Prism.ConcavePL γ₁ := by
    refine ⟨τ₀.attach.image g1, hne₀.attach.image g1, fun w => ?_⟩
    rw [hγ₁def]
    exact (Finset.inf'_image (hne₀.attach.image g1) (fun f => f w)).symm
  have hFle : ∀ w ∈ F, γ₀ w ≤ γ₁ w := fun w hw => hw
  have hFfr : ∀ w ∈ frontier F, γ₀ w = γ₁ w := by
    intro w hw
    have hw' : w ∈ closure F \ interior F := by rw [closure_diff_interior]; exact hw
    have hwF : w ∈ F := by rw [hFcompact.isClosed.closure_eq] at hw'; exact hw'.1
    have hni : w ∉ interior F := hw'.2
    have hsub : {w' : PL.E q | γ₀ w' < γ₁ w'} ⊆ F := fun w' hw' => show γ₀ w' ≤ γ₁ w' from le_of_lt hw'
    have hmem : w ∉ {w' : PL.E q | γ₀ w' < γ₁ w'} := by
      intro hc
      refine hni (mem_interior_iff_mem_nhds.mpr ?_)
      exact Filter.mem_of_superset ((isOpen_lt hγ₀cont hγ₁cont).mem_nhds hc) hsub
    exact le_antisymm hwF (not_lt.mp hmem)
  -- ============ (c) facets opposite τ₁ ↦ floor ============
  have xfun_eq : ∀ (w : PL.E q) (t : ℝ), xfun w t = ∑ v ∈ S, muF v (w, t) • v := by
    intro w t
    rw [hxfundef, Finset.sum_subtype S (fun _ => Iff.rfl) (fun v => muF v (w, t) • v)]
    apply Finset.sum_congr rfl
    intro v _
    rw [muF_of_mem' v.1 v.2 (w, t)]
  have h5a : T '' (⋃ w ∈ τ₁, PL.simp (S.erase w)) =
      {y : PL.E (n - q - 1) × (PL.E q × ℝ) | y.1 = 0 ∧ y.2.1 ∈ F ∧ y.2.2 = γ₀ y.2.1} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Set.mem_iUnion] at hx
      obtain ⟨w, hx⟩ := hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨hw, hxw⟩ := hx
      have hxS : x ∈ PL.simp S := PL.simp_mono (Finset.erase_subset w S) hxw
      have hxD : x ∈ (D:Set (PL.E n)) := PL.simp_subset_affineSpan S hxS
      have hlam0 : lamF w x = 0 := by
        obtain ⟨μ, hμ0, hμ1, hμx⟩ := (mem_simp_gen (S.erase w) x).mp hxw
        rw [← hμx, affineComb (lamF w) (S.erase w) μ hμ1]
        apply Finset.sum_eq_zero
        intro b hb
        rw [lamF_neq w (hmem1 w hw) b (Finset.mem_of_mem_erase hb) (Finset.mem_erase.mp hb).1.symm,
          mul_zero]
      have hg : g0 ⟨w, hw⟩ (z x) = tau x := by
        rw [g0_eval ⟨w, hw⟩ x hxD, hlam0]; ring
      have hgamma : γ₀ (z x) = tau x := by
        apply le_antisymm (g0_le x hxS)
        change tau x ≤ τ₁.attach.sup' hne₁.attach (fun j => g0 j (z x))
        calc tau x = g0 ⟨w, hw⟩ (z x) := hg.symm
          _ ≤ _ := Finset.le_sup' (fun j : ↥τ₁ => g0 j (z x))
              (by rw [Finset.attach_eq_univ]; exact Finset.mem_univ _)
      rw [hTD x hxD]
      refine ⟨rfl, ?_, ?_⟩
      · show γ₀ (z x) ≤ γ₁ (z x)
        rw [hgamma]; exact g1_ge x hxS
      · exact hgamma.symm
    · rintro ⟨h1, h2, h3⟩
      obtain ⟨j, hj, hjsup⟩ := Finset.exists_mem_eq_sup' hne₁.attach (fun j : ↥τ₁ => g0 j y.2.1)
      have hj1 : j.1 ∈ τ₁ := j.2
      have hgj : g0 j y.2.1 = y.2.2 := by
        rw [h3, hγ₀def]; exact hjsup.symm
      have hmu0 : mu ⟨j.1, hmem1 j.1 hj1⟩ (y.2.1, y.2.2) = 0 := by
        have hnot : ¬ (j.1 ∈ τ₀) := fun hc => (Finset.disjoint_left.mp hdisj) hc hj1
        rw [hmudef]; simp only [dif_neg hnot]
        rw [show Bfun j.1 y.2.1 + (y.2.2 - sumB y.2.1) / (τ₁.card : ℝ)
            = (y.2.2 - g0 ⟨j.1, hj1⟩ y.2.1) / (τ₁.card : ℝ) from by
          rw [show g0 ⟨j.1, hj1⟩ y.2.1 = sumB y.2.1 - (τ₁.card : ℝ) * Bfun j.1 y.2.1 from by
            rw [hg0def]; simp]
          field_simp; ring]
        rw [hgj]; simp
      refine ⟨xfun y.2.1 y.2.2, ?_, ?_⟩
      · rw [Set.mem_iUnion]
        refine ⟨j.1, ?_⟩
        rw [Set.mem_iUnion]
        refine ⟨hj1, ?_⟩
        refine (mem_simp_gen (S.erase j.1) (xfun y.2.1 y.2.2)).mpr
          ⟨fun v => muF v (y.2.1, y.2.2), ?_, ?_, ?_⟩
        · intro v hv
          show 0 ≤ muF v (y.2.1, y.2.2)
          rw [muF_of_mem' v (Finset.mem_of_mem_erase hv)]
          exact mu_nonneg y.2.1 y.2.2 h2 (le_of_eq h3.symm)
            ((le_of_eq h3).trans (show γ₀ y.2.1 ≤ γ₁ y.2.1 from h2))
            ⟨v, Finset.mem_of_mem_erase hv⟩
        · have hall : (∑ v ∈ S, muF v (y.2.1, y.2.2)) = 1 := by
            rw [Finset.sum_subtype S (fun _ => Iff.rfl) (fun v => muF v (y.2.1, y.2.2))]
            rw [show (∑ v : ↥S, muF v.1 (y.2.1, y.2.2)) = ∑ v : ↥S, mu v (y.2.1, y.2.2) from
              Finset.sum_congr rfl (fun v _ => muF_of_mem' v.1 v.2 (y.2.1, y.2.2))]
            exact mu_sum y.2.1 y.2.2
          have hjmem : j.1 ∈ S := hmem1 j.1 hj1
          rw [Finset.sum_erase_eq_sub hjmem, hall,
            show muF j.1 (y.2.1, y.2.2) = 0 from by
              rw [muF_of_mem' j.1 hjmem]; exact hmu0]
          ring
        · have hall : (∑ v ∈ S, muF v (y.2.1, y.2.2) • v) = xfun y.2.1 y.2.2 := (xfun_eq _ _).symm
          have hjmem : j.1 ∈ S := hmem1 j.1 hj1
          rw [Finset.sum_erase_eq_sub hjmem, hall,
            show muF j.1 (y.2.1, y.2.2) • j.1 = 0 from by
              rw [muF_of_mem' j.1 hjmem, hmu0, zero_smul]]
          simp
      · have hxd : xfun y.2.1 y.2.2 ∈ (D:Set (PL.E n)) := xfun_mem _ _
        rw [hTD _ hxd, z_xfun, tau_xfun]
        exact Prod.ext h1.symm (Prod.ext rfl rfl)
  -- ============ (d) facets opposite τ₀ ↦ top ============
  have h5b : T '' (⋃ w ∈ τ₀, PL.simp (S.erase w)) =
      {y : PL.E (n - q - 1) × (PL.E q × ℝ) | y.1 = 0 ∧ y.2.1 ∈ F ∧ y.2.2 = γ₁ y.2.1} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Set.mem_iUnion] at hx
      obtain ⟨w, hx⟩ := hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨hw, hxw⟩ := hx
      have hxS : x ∈ PL.simp S := PL.simp_mono (Finset.erase_subset w S) hxw
      have hxD : x ∈ (D:Set (PL.E n)) := PL.simp_subset_affineSpan S hxS
      have hlam0 : lamF w x = 0 := by
        obtain ⟨μ, hμ0, hμ1, hμx⟩ := (mem_simp_gen (S.erase w) x).mp hxw
        rw [← hμx, affineComb (lamF w) (S.erase w) μ hμ1]
        apply Finset.sum_eq_zero
        intro b hb
        rw [lamF_neq w (hmem0 w hw) b (Finset.mem_of_mem_erase hb) (Finset.mem_erase.mp hb).1.symm,
          mul_zero]
      have hg : g1 ⟨w, hw⟩ (z x) = tau x := by
        rw [g1_eval ⟨w, hw⟩ x hxD, hlam0]; ring
      have hgamma : γ₁ (z x) = tau x := by
        apply le_antisymm _ (g1_ge x hxS)
        change τ₀.attach.inf' hne₀.attach (fun i => g1 i (z x)) ≤ tau x
        calc _ ≤ g1 ⟨w, hw⟩ (z x) := Finset.inf'_le (fun i : ↥τ₀ => g1 i (z x))
              (by rw [Finset.attach_eq_univ]; exact Finset.mem_univ _)
          _ = tau x := hg
      rw [hTD x hxD]
      refine ⟨rfl, ?_, ?_⟩
      · show γ₀ (z x) ≤ γ₁ (z x)
        rw [hgamma]; exact g0_le x hxS
      · exact hgamma.symm
    · rintro ⟨h1, h2, h3⟩
      obtain ⟨i, hi, hiinf⟩ := Finset.exists_mem_eq_inf' hne₀.attach (fun i : ↥τ₀ => g1 i y.2.1)
      have hi1 : i.1 ∈ τ₀ := i.2
      have hgi : g1 i y.2.1 = y.2.2 := by
        rw [h3, hγ₁def]; exact hiinf.symm
      have hmu0 : mu ⟨i.1, hmem0 i.1 hi1⟩ (y.2.1, y.2.2) = 0 := by
        rw [hmudef]; simp only [dif_pos hi1]
        rw [show Afun i.1 y.2.1 + (1 - y.2.2 - sumA y.2.1) / (τ₀.card : ℝ)
            = (g1 ⟨i.1, hi1⟩ y.2.1 - y.2.2) / (τ₀.card : ℝ) from by
          rw [show g1 ⟨i.1, hi1⟩ y.2.1 = 1 - sumA y.2.1 + (τ₀.card : ℝ) * Afun i.1 y.2.1 from by
            rw [hg1def]; simp]
          field_simp; ring]
        rw [hgi]; simp
      refine ⟨xfun y.2.1 y.2.2, ?_, ?_⟩
      · rw [Set.mem_iUnion]
        refine ⟨i.1, ?_⟩
        rw [Set.mem_iUnion]
        refine ⟨hi1, ?_⟩
        refine (mem_simp_gen (S.erase i.1) (xfun y.2.1 y.2.2)).mpr
          ⟨fun v => muF v (y.2.1, y.2.2), ?_, ?_, ?_⟩
        · intro v hv
          show 0 ≤ muF v (y.2.1, y.2.2)
          rw [muF_of_mem' v (Finset.mem_of_mem_erase hv)]
          exact mu_nonneg y.2.1 y.2.2 h2
            ((show γ₀ y.2.1 ≤ γ₁ y.2.1 from h2).trans (le_of_eq h3.symm)) (le_of_eq h3)
            ⟨v, Finset.mem_of_mem_erase hv⟩
        · have hall : (∑ v ∈ S, muF v (y.2.1, y.2.2)) = 1 := by
            rw [Finset.sum_subtype S (fun _ => Iff.rfl) (fun v => muF v (y.2.1, y.2.2))]
            rw [show (∑ v : ↥S, muF v.1 (y.2.1, y.2.2)) = ∑ v : ↥S, mu v (y.2.1, y.2.2) from
              Finset.sum_congr rfl (fun v _ => muF_of_mem' v.1 v.2 (y.2.1, y.2.2))]
            exact mu_sum y.2.1 y.2.2
          have himem : i.1 ∈ S := hmem0 i.1 hi1
          rw [Finset.sum_erase_eq_sub himem, hall,
            show muF i.1 (y.2.1, y.2.2) = 0 from by
              rw [muF_of_mem' i.1 himem]; exact hmu0]
          ring
        · have hall : (∑ v ∈ S, muF v (y.2.1, y.2.2) • v) = xfun y.2.1 y.2.2 := (xfun_eq _ _).symm
          have himem : i.1 ∈ S := hmem0 i.1 hi1
          rw [Finset.sum_erase_eq_sub himem, hall,
            show muF i.1 (y.2.1, y.2.2) • i.1 = 0 from by
              rw [muF_of_mem' i.1 himem, hmu0, zero_smul]]
          simp
      · have hxd : xfun y.2.1 y.2.2 ∈ (D:Set (PL.E n)) := xfun_mem _ _
        rw [hTD _ hxd, z_xfun, tau_xfun]
        exact Prod.ext h1.symm (Prod.ext rfl rfl)
  exact ⟨T, F, γ₀, γ₁, hFcompact, hFconvex, hγ₀cont, hγ₁cont, hγ₀PL, hγ₁PL, hFle, hFfr,
    h4, h5a, h5b⟩


end
end Work.Geo.Prism.Join
