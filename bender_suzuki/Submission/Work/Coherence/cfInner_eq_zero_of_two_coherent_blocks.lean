import Mathlib
import Submission.Work.Coherence.All
import Submission.Work.CharCore.Coherence
import Submission.Work.Coherence.cross_core
import Submission.Work.Coherence.cfInner_expand_zsmul

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

noncomputable section

open Classical

namespace Work.Coherence

/-- The degree-difference `n' • x - n • x'` of two elements `x, x'` of a finite set `S` of
characters, where `n = x 1` and `n' = x' 1` are the degrees, lies in the degree-zero lattice
`ℤ[S]⁰`.  (The coefficients are exactly the degrees, so that the value at `1` cancels.) -/
lemma zsmul_deg_sub_mem_zSpan0 {H : Type*} [Group H] [Fintype H] {S : Finset (H → ℂ)}
    {x x' : H → ℂ} (hx : x ∈ S) (hx' : x' ∈ S) {n n' : ℕ}
    (hn : x 1 = (n : ℂ)) (hn' : x' 1 = (n' : ℂ)) :
    (n' : ℤ) • x - (n : ℤ) • x' ∈ ZSpan0 S := by
  rw [mem_zSpan0]
  refine ⟨AddSubgroup.sub_mem _
      (AddSubgroup.zsmul_mem _ (self_mem_zSpan hx) (n' : ℤ))
      (AddSubgroup.zsmul_mem _ (self_mem_zSpan hx') (n : ℤ)), ?_⟩
  have h1 : ((n' : ℤ) • x - (n : ℤ) • x') 1 = (n' : ℂ) * (x 1) - (n : ℂ) * (x' 1) := by
    simp [zsmul_eq_mul]
  rw [h1, hn, hn']
  ring

theorem cfInner_eq_zero_of_two_coherent_blocks {H G : Type*} [Group H] [Fintype H] [Group G] [Fintype G]
    {S X Y : Finset (H → ℂ)} {τ σ ρ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hXY : Disjoint X Y) (hsub : X ∪ Y ⊆ S) (hIrr : ∀ x ∈ S, x ∈ Work.CharCore.Irr H)
    (hτ : Work.Coherence.IsometryOn S τ) (hτV : ∀ α ∈ Work.Coherence.ZSpan0 S, τ α 1 = 0)
    (hσ0 : ∀ α ∈ Work.Coherence.ZSpan0 X, σ α = τ α) (hσ : Work.Coherence.IsometryOnAll X σ)
    (hδ : ∃ δ : ℂ, δ * δ = 1 ∧ ∀ x ∈ X, (δ • σ x) ∈ Work.CharCore.Irr G)
    (hρ0 : ∀ α ∈ Work.Coherence.ZSpan0 Y, ρ α = τ α) (hρ : Work.Coherence.IsometryOnAll Y ρ)
    (hε : ∃ ε : ℂ, ε * ε = 1 ∧ ∀ y ∈ Y, (ε • ρ y) ∈ Work.CharCore.Irr G)
    (hcardX : 2 ≤ X.card) (hcardY : 2 ≤ Y.card) :
    ∀ x ∈ X, ∀ y ∈ Y, Work.Coherence.cfInner (σ x) (ρ y) = 0 := by
  classical
  obtain ⟨δ, hδ2, hδIrr⟩ := hδ
  obtain ⟨ε, hε2, hεIrr⟩ := hε
  have hδcases : δ = 1 ∨ δ = -1 := mul_self_eq_one_iff.mp hδ2
  have hεcases : ε = 1 ∨ ε = -1 := mul_self_eq_one_iff.mp hε2
  have hδne : δ ≠ 0 := by rcases hδcases with h | h <;> rw [h] <;> norm_num
  have hεne : ε ≠ 0 := by rcases hεcases with h | h <;> rw [h] <;> norm_num
  have hconjε : starRingEnd ℂ ε = ε := by rcases hεcases with h | h <;> simp [h]
  intro x hx y hy
  -- both blocks sit inside `S`
  have hXS : X ⊆ S := fun z hz => hsub (Finset.mem_union_left Y hz)
  have hYS : Y ⊆ S := fun z hz => hsub (Finset.mem_union_right X hz)
  have hxS : x ∈ S := hXS hx
  have hyS : y ∈ S := hYS hy
  -- the four irreducible characters of `H` involved
  have hxIrr : x ∈ Irr H := (CharCore.mem_Irr_iff_coherence).mp (hIrr x hxS)
  have hyIrr : y ∈ Irr H := (CharCore.mem_Irr_iff_coherence).mp (hIrr y hyS)
  -- the images under `δ • σ` and `ε • ρ` are irreducible characters of `G`
  have hχxIrr : (δ • σ x) ∈ Irr G := (CharCore.mem_Irr_iff_coherence).mp (hδIrr x hx)
  have hψyIrr : (ε • ρ y) ∈ Irr G := (CharCore.mem_Irr_iff_coherence).mp (hεIrr y hy)
  -- a second element in each block
  obtain ⟨x', hx'X, hx'ne⟩ := Finset.exists_mem_ne (s := X) (by omega) x
  obtain ⟨y', hy'Y, hy'ne⟩ := Finset.exists_mem_ne (s := Y) (by omega) y
  have hx'S : x' ∈ S := hXS hx'X
  have hy'S : y' ∈ S := hYS hy'Y
  have hx'Irr : x' ∈ Irr H := (CharCore.mem_Irr_iff_coherence).mp (hIrr x' hx'S)
  have hy'Irr : y' ∈ Irr H := (CharCore.mem_Irr_iff_coherence).mp (hIrr y' hy'S)
  have hχx'Irr : (δ • σ x') ∈ Irr G := (CharCore.mem_Irr_iff_coherence).mp (hδIrr x' hx'X)
  have hψy'Irr : (ε • ρ y') ∈ Irr G := (CharCore.mem_Irr_iff_coherence).mp (hεIrr y' hy'Y)
  -- the degrees are positive integers
  obtain ⟨nx, hnx, hnx1⟩ := irr_degree_pos hxIrr
  obtain ⟨nx', hnx', hnx'1⟩ := irr_degree_pos hx'Irr
  obtain ⟨ny, hny, hny1⟩ := irr_degree_pos hyIrr
  obtain ⟨ny', hny', hny'1⟩ := irr_degree_pos hy'Irr
  -- irreducible characters on the two sides are orthogonal
  have hxy0 : cfInner x y = 0 := by
    rw [irr_cfInner hxIrr hyIrr]
    exact ite_eq_right (fun h => (Finset.disjoint_left.mp hXY hx) (by rw [← h] at hy; exact hy))
  have hxy'0 : cfInner x y' = 0 := by
    rw [irr_cfInner hxIrr hy'Irr]
    exact ite_eq_right (fun h => (Finset.disjoint_left.mp hXY hx) (by rw [← h] at hy'Y; exact hy'Y))
  have hx'y0 : cfInner x' y = 0 := by
    rw [irr_cfInner hx'Irr hyIrr]
    exact ite_eq_right (fun h => (Finset.disjoint_left.mp hXY hx'X) (by rw [← h] at hy; exact hy))
  have hx'y'0 : cfInner x' y' = 0 := by
    rw [irr_cfInner hx'Irr hy'Irr]
    exact ite_eq_right (fun h => (Finset.disjoint_left.mp hXY hx'X) (by rw [← h] at hy'Y; exact hy'Y))
  -- the degree-weighted differences lie in `ℤ[X]⁰` and `ℤ[Y]⁰`, hence in `ℤ[S]⁰`
  have hu0 : (nx' : ℤ) • x - (nx : ℤ) • x' ∈ ZSpan0 X :=
    zsmul_deg_sub_mem_zSpan0 hx hx'X hnx1 hnx'1
  have hv0 : (ny' : ℤ) • y - (ny : ℤ) • y' ∈ ZSpan0 Y :=
    zsmul_deg_sub_mem_zSpan0 hy hy'Y hny1 hny'1
  have huS : (nx' : ℤ) • x - (nx : ℤ) • x' ∈ ZSpan0 S := zSpan0_mono hXS hu0
  have hvS : (ny' : ℤ) • y - (ny : ℤ) • y' ∈ ZSpan0 S := zSpan0_mono hYS hv0
  -- the isometry `τ` makes the two differences orthogonal
  have hcross : cfInner (σ ((nx' : ℤ) • x - (nx : ℤ) • x'))
      (ρ ((ny' : ℤ) • y - (ny : ℤ) • y')) = 0 := by
    have h1 : σ ((nx' : ℤ) • x - (nx : ℤ) • x') = τ ((nx' : ℤ) • x - (nx : ℤ) • x') :=
      hσ0 _ hu0
    have h2 : ρ ((ny' : ℤ) • y - (ny : ℤ) • y') = τ ((ny' : ℤ) • y - (ny : ℤ) • y') :=
      hρ0 _ hv0
    have h3 : cfInner (τ ((nx' : ℤ) • x - (nx : ℤ) • x'))
        (τ ((ny' : ℤ) • y - (ny : ℤ) • y')) =
        cfInner ((nx' : ℤ) • x - (nx : ℤ) • x') ((ny' : ℤ) • y - (ny : ℤ) • y') :=
      hτ.inner_eq _ huS _ hvS
    rw [h1, h2, h3, cfInner_expand_zsmul, hxy0, hxy'0, hx'y0, hx'y'0]
    ring
  -- expand in terms of `⟨σ x, ρ y⟩` etc.
  have hσu : σ ((nx' : ℤ) • x - (nx : ℤ) • x') = (nx' : ℤ) • σ x - (nx : ℤ) • σ x' := by
    rw [map_sub, map_zsmul, map_zsmul]
  have hρv : ρ ((ny' : ℤ) • y - (ny : ℤ) • y') = (ny' : ℤ) • ρ y - (ny : ℤ) • ρ y' := by
    rw [map_sub, map_zsmul, map_zsmul]
  -- re-insert the scalars `δ` and `ε`
  have hσxsmul : σ x = δ • (δ • σ x) := by rw [smul_smul, hδ2, one_smul]
  have hσx'smul : σ x' = δ • (δ • σ x') := by rw [smul_smul, hδ2, one_smul]
  have hρysmul : ρ y = ε • (ε • ρ y) := by rw [smul_smul, hε2, one_smul]
  have hρy'smul : ρ y' = ε • (ε • ρ y') := by rw [smul_smul, hε2, one_smul]
  have hM11 : cfInner (σ x) (ρ y) = δ * starRingEnd ℂ ε * cfInner (δ • σ x) (ε • ρ y) := by
    conv_lhs => rw [hσxsmul, hρysmul, cfInner_smul_left, cfInner_smul_right]
    rw [hconjε]
    ring
  have hM12 : cfInner (σ x) (ρ y') = δ * starRingEnd ℂ ε * cfInner (δ • σ x) (ε • ρ y') := by
    conv_lhs => rw [hσxsmul, hρy'smul, cfInner_smul_left, cfInner_smul_right]
    rw [hconjε]
    ring
  have hM21 : cfInner (σ x') (ρ y) = δ * starRingEnd ℂ ε * cfInner (δ • σ x') (ε • ρ y) := by
    conv_lhs => rw [hσx'smul, hρysmul, cfInner_smul_left, cfInner_smul_right]
    rw [hconjε]
    ring
  have hM22 : cfInner (σ x') (ρ y') = δ * starRingEnd ℂ ε * cfInner (δ • σ x') (ε • ρ y') := by
    conv_lhs => rw [hσx'smul, hρy'smul, cfInner_smul_left, cfInner_smul_right]
    rw [hconjε]
    ring
  -- the signed relation for the four entries of the image Gram matrix of the two irreducible
  -- characters
  have hexp : (nx' : ℂ) * (ny' : ℂ) * cfInner (δ • σ x) (ε • ρ y)
      - (nx' : ℂ) * (ny : ℂ) * cfInner (δ • σ x) (ε • ρ y')
      - (nx : ℂ) * (ny' : ℂ) * cfInner (δ • σ x') (ε • ρ y)
      + (nx : ℂ) * (ny : ℂ) * cfInner (δ • σ x') (ε • ρ y') = 0 := by
    have h := hcross
    rw [hσu, hρv, cfInner_expand_zsmul] at h
    rw [hM11, hM12, hM21, hM22] at h
    have hne : δ * starRingEnd ℂ ε ≠ 0 := by
      rw [hconjε]
      exact mul_ne_zero hδne hεne
    have h2 : (δ * starRingEnd ℂ ε) *
        ((nx' : ℂ) * (ny' : ℂ) * cfInner (δ • σ x) (ε • ρ y)
        - (nx' : ℂ) * (ny : ℂ) * cfInner (δ • σ x) (ε • ρ y')
        - (nx : ℂ) * (ny' : ℂ) * cfInner (δ • σ x') (ε • ρ y)
        + (nx : ℂ) * (ny : ℂ) * cfInner (δ • σ x') (ε • ρ y')) = 0 := by
      rw [← h]
      push_cast
      ring
    exact (mul_eq_zero.mp h2).resolve_left hne
  -- the four irreducible characters on the `G`-side are distinct
  have hσxx : cfInner (σ x) (σ x) = 1 := by
    rw [hσ.inner_eq x (self_mem_zSpan hx) x (self_mem_zSpan hx),
      irr_cfInner hxIrr hxIrr, ite_eq_left rfl]
  have hσxx' : cfInner (σ x) (σ x') = 0 := by
    rw [hσ.inner_eq x (self_mem_zSpan hx) x' (self_mem_zSpan hx'X),
      irr_cfInner hxIrr hx'Irr, ite_eq_right (fun h => hx'ne h.symm)]
  have hσne : σ x ≠ σ x' := by
    intro hcon
    have h : cfInner (σ x) (σ x') = 1 := by rw [← hcon]; exact hσxx
    rw [hσxx'] at h
    exact one_ne_zero h.symm
  have hχne : (δ • σ x) ≠ (δ • σ x') := by
    intro hcon
    refine hσne (funext fun g => ?_)
    have hg := congrFun hcon g
    simp only [Pi.smul_apply, smul_eq_mul] at hg
    exact mul_left_cancel₀ hδne hg
  have hρyy : cfInner (ρ y) (ρ y) = 1 := by
    rw [hρ.inner_eq y (self_mem_zSpan hy) y (self_mem_zSpan hy),
      irr_cfInner hyIrr hyIrr, ite_eq_left rfl]
  have hρyy' : cfInner (ρ y) (ρ y') = 0 := by
    rw [hρ.inner_eq y (self_mem_zSpan hy) y' (self_mem_zSpan hy'Y),
      irr_cfInner hyIrr hy'Irr, ite_eq_right (fun h => hy'ne h.symm)]
  have hρne : ρ y ≠ ρ y' := by
    intro hcon
    have h : cfInner (ρ y) (ρ y') = 1 := by rw [← hcon]; exact hρyy
    rw [hρyy'] at h
    exact one_ne_zero h.symm
  have hψne : (ε • ρ y) ≠ (ε • ρ y') := by
    intro hcon
    refine hρne (funext fun g => ?_)
    have hg := congrFun hcon g
    simp only [Pi.smul_apply, smul_eq_mul] at hg
    exact mul_left_cancel₀ hεne hg
  -- the arithmetic core
  have hcore : cfInner (δ • σ x) (ε • ρ y) = 0 :=
    cross_core hχxIrr hχx'Irr hψyIrr hψy'Irr hχne hψne hnx' hnx hny' hny hexp
  rw [hM11, hcore, mul_zero]

end Work.Coherence
