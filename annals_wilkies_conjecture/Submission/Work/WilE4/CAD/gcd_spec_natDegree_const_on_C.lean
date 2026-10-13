/-
  WilE4 / CAD — constancy of the degree of the gcd of two specialisations.

  `gcd_spec_natDegree_const_on_C`: if on a set `C` of base points

  * the signs of all coefficients (of index at most `D`) of every specialisation `spec (P i) x` are
    constant, and
  * the signs of *all* determinants of submatrices ("minors") of every Sylvester matrix
    `sylvester (spec (P i) x) (spec (P j) x) a b` with `a, b ≤ D` are constant,

  then the `natDegree` of `gcd (spec (P i) x) (spec (P j) x)` is constant on `C`.

  The mathematical content is the classical Sylvester rank formula
  `rank (sylvester f g f.natDegree g.natDegree) = f.natDegree + g.natDegree - deg (gcd f g)`
  together with the fact that the rank of a matrix is the largest size of a nonvanishing minor
  (`rank_eq_of_minors_det_eq_zero_iff`).  The rank formula is proved here from scratch, using the
  identification of the Sylvester matrix with the matrix of `Polynomial.sylvesterMap`
  (`rank_sylvester_eq_finrank_range`) and the explicit description of the kernel of that map
  (`gsc_range_kerIota`).
-/
import Mathlib
import Submission.Work.WilE4.CAD.Proj
import Submission.Work.WilE4.CAD.signConst_data
import Submission.Work.WilE4.CAD.cell_preconnected
import Submission.Work.WilE4.CAD.mul_mem_degreeLT
import Submission.Work.WilE4.CAD.mem_degreeLT_of_mul_mem_degreeLT
import Submission.Work.WilE4.CAD.rank_sylvester_eq_finrank_range
import Submission.Work.WilE4.CAD.rank_eq_of_minors_det_eq_zero_iff

set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilE4.CAD

open MvPolynomial Polynomial

/-! ## The Sylvester rank formula

For nonzero `f g : ℝ[X]`, the rank of the Sylvester matrix taken at the exact degrees is
`deg f + deg g - deg (gcd f g)`.  Mathlib identifies that matrix with the matrix of the linear map
`Polynomial.sylvesterMap f g : ℝ[X]_{<m} × ℝ[X]_{<n} → ℝ[X]_{<m+n}`, `(p, q) ↦ f * q + g * p`
(`Polynomial.toMatrix_sylvesterMap'`), so its rank is the dimension of the range of that map and
rank–nullity reduces the statement to `dim ker = deg (gcd f g)`.  Writing `d = gcd f g`,
`f = d * (f / d)`, `g = d * (g / d)` with coprime quotients, the kernel consists exactly of the
pairs `(u * c, -(w * c))` with `c ∈ ℝ[X]_{<deg d}` — the range of the injective map
`gsc_kerIota`. -/

lemma gsc_finrank_degreeLT (k : ℕ) : Module.finrank ℝ (Polynomial.degreeLT ℝ k) = k := by
  rw [(Polynomial.degreeLTEquiv ℝ k).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin]

lemma gsc_deg_fst (f g : Polynomial ℝ) (hf : f ≠ 0) :
    (f / gcd f g).natDegree + (gcd f g).natDegree = f.natDegree := by
  rw [← Polynomial.natDegree_mul (left_div_gcd_ne_zero hf) (gcd_ne_zero_of_left hf), mul_comm,
    EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_left hf) (gcd_dvd_left f g)]

lemma gsc_deg_snd (f g : Polynomial ℝ) (hf : f ≠ 0) (hg : g ≠ 0) :
    (g / gcd f g).natDegree + (gcd f g).natDegree = g.natDegree := by
  rw [← Polynomial.natDegree_mul (right_div_gcd_ne_zero hg) (gcd_ne_zero_of_left hf), mul_comm,
    EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_left hf) (gcd_dvd_right f g)]

/-- The linear map `c ↦ (f / gcd f g * c, -(g / gcd f g * c))`, whose range is the kernel of the
Sylvester map of `f` and `g`. -/
noncomputable def gsc_kerIota (f g : Polynomial ℝ) (hf : f ≠ 0) (hg : g ≠ 0) :
    Polynomial.degreeLT ℝ (gcd f g).natDegree →ₗ[ℝ]
      (Polynomial.degreeLT ℝ f.natDegree × Polynomial.degreeLT ℝ g.natDegree) where
  toFun c :=
    (⟨(f / gcd f g) * (c : Polynomial ℝ), mul_mem_degreeLT (gsc_deg_fst f g hf) c.2⟩,
      ⟨-((g / gcd f g) * (c : Polynomial ℝ)),
        neg_mem (mul_mem_degreeLT (gsc_deg_snd f g hf hg) c.2)⟩)
  map_add' c c' := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change (f / gcd f g) * ((c : Polynomial ℝ) + (c' : Polynomial ℝ)) =
        (f / gcd f g) * (c : Polynomial ℝ) + (f / gcd f g) * (c' : Polynomial ℝ)
      ring
    · change -((g / gcd f g) * ((c : Polynomial ℝ) + (c' : Polynomial ℝ))) =
        -((g / gcd f g) * (c : Polynomial ℝ)) + -((g / gcd f g) * (c' : Polynomial ℝ))
      ring
  map_smul' r c := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change (f / gcd f g) * (r • (c : Polynomial ℝ)) =
        r • ((f / gcd f g) * (c : Polynomial ℝ))
      rw [Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul]
      ring
    · change -((g / gcd f g) * (r • (c : Polynomial ℝ))) =
        r • (-((g / gcd f g) * (c : Polynomial ℝ)))
      rw [Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul]
      ring

@[simp] lemma gsc_kerIota_fst (f g : Polynomial ℝ) (hf : f ≠ 0) (hg : g ≠ 0) (c) :
    ((gsc_kerIota f g hf hg c).1 : Polynomial ℝ) = (f / gcd f g) * (c : Polynomial ℝ) := rfl

@[simp] lemma gsc_kerIota_snd (f g : Polynomial ℝ) (hf : f ≠ 0) (hg : g ≠ 0) (c) :
    ((gsc_kerIota f g hf hg c).2 : Polynomial ℝ) = -((g / gcd f g) * (c : Polynomial ℝ)) := rfl

lemma gsc_kerIota_injective (f g : Polynomial ℝ) (hf : f ≠ 0) (hg : g ≠ 0) :
    Function.Injective (gsc_kerIota f g hf hg) := by
  intro c c' h
  have h1 : (f / gcd f g) * (c : Polynomial ℝ) = (f / gcd f g) * (c' : Polynomial ℝ) := by
    rw [← gsc_kerIota_fst f g hf hg c, ← gsc_kerIota_fst f g hf hg c', h]
  exact Subtype.ext (mul_left_cancel₀ (left_div_gcd_ne_zero hf) h1)

lemma gsc_range_kerIota (f g : Polynomial ℝ) (hf : f ≠ 0) (hg : g ≠ 0) :
    LinearMap.range (gsc_kerIota f g hf hg) =
      LinearMap.ker (Polynomial.sylvesterMap f g (le_refl f.natDegree) (le_refl g.natDegree)) := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    rw [Submodule.coe_zero]
    show f * (-((g / gcd f g) * (c : Polynomial ℝ)))
      + g * ((f / gcd f g) * (c : Polynomial ℝ)) = 0
    set c' : Polynomial ℝ := (c : Polynomial ℝ) with hc'
    set d : Polynomial ℝ := gcd f g with hdd
    set u : Polynomial ℝ := f / d with hu
    set w : Polynomial ℝ := g / d with hw
    have hfe : f = d * u := by
      rw [hu, hdd, EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_left hf) (gcd_dvd_left f g)]
    have hge : g = d * w := by
      rw [hw, hdd, EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_left hf) (gcd_dvd_right f g)]
    rw [hfe, hge]
    ring
  · intro hx
    rw [LinearMap.mem_ker] at hx
    obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := x
    have hp0 : f * q + g * p = 0 := by
      have h := congrArg (fun y : Polynomial.degreeLT ℝ (f.natDegree + g.natDegree) =>
        (y : Polynomial ℝ)) hx
      simpa using h
    have hd : gcd f g ≠ 0 := gcd_ne_zero_of_left hf
    have hu : f / gcd f g ≠ 0 := left_div_gcd_ne_zero hf
    have hfe : gcd f g * (f / gcd f g) = f :=
      EuclideanDomain.mul_div_cancel' hd (gcd_dvd_left f g)
    have hge : gcd f g * (g / gcd f g) = g :=
      EuclideanDomain.mul_div_cancel' hd (gcd_dvd_right f g)
    have hcop : IsCoprime (f / gcd f g) (g / gcd f g) :=
      isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hd
    have h1 : (f / gcd f g) * q + (g / gcd f g) * p = 0 := by
      have h2 : gcd f g * ((f / gcd f g) * q + (g / gcd f g) * p) = 0 := by
        rw [mul_add, ← mul_assoc, ← mul_assoc, hfe, hge]
        exact hp0
      exact (mul_eq_zero.mp h2).resolve_left hd
    have hdvd : (f / gcd f g) ∣ p := by
      apply hcop.dvd_of_dvd_mul_left
      have h3 : (f / gcd f g) * q = -((g / gcd f g) * p) := by linear_combination h1
      exact dvd_neg.mp (h3 ▸ dvd_mul_right (f / gcd f g) q)
    refine ⟨⟨p / (f / gcd f g), ?_⟩, ?_⟩
    · have hdu : (f / gcd f g).natDegree + (gcd f g).natDegree = f.natDegree :=
        gsc_deg_fst f g hf
      have hmul : (f / gcd f g) * (p / (f / gcd f g)) = p :=
        EuclideanDomain.mul_div_cancel' hu hdvd
      by_cases hr : p / (f / gcd f g) = 0
      · rw [hr]; exact Submodule.zero_mem _
      · exact mem_degreeLT_of_mul_mem_degreeLT hu hdu hr (by rw [hmul]; exact hp)
    · refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · exact EuclideanDomain.mul_div_cancel' hu hdvd
      · have h4 : (f / gcd f g) * (q + (g / gcd f g) * (p / (f / gcd f g))) = 0 := by
          rw [← EuclideanDomain.mul_div_cancel' hu hdvd] at h1
          rw [mul_add]
          linear_combination h1
        have h5 : q + (g / gcd f g) * (p / (f / gcd f g)) = 0 :=
          (mul_eq_zero.mp h4).resolve_left hu
        exact (add_eq_zero_iff_eq_neg.mp h5).symm

lemma gsc_finrank_ker_sylvesterMap (f g : Polynomial ℝ) (hf : f ≠ 0) (hg : g ≠ 0) :
    Module.finrank ℝ
        (LinearMap.ker (Polynomial.sylvesterMap f g (le_refl f.natDegree) (le_refl g.natDegree)))
      = (gcd f g).natDegree := by
  rw [← gsc_range_kerIota f g hf hg,
    LinearMap.finrank_range_of_inj (gsc_kerIota_injective f g hf hg), gsc_finrank_degreeLT]

/-- **The Sylvester rank formula.**  For nonzero `f g : ℝ[X]` the rank of the Sylvester matrix
taken at the exact degrees is `deg f + deg g - deg (gcd f g)`. -/
theorem gsc_rank_sylvester (f g : Polynomial ℝ) (hf : f ≠ 0) (hg : g ≠ 0) :
    (Polynomial.sylvester f g f.natDegree g.natDegree).rank
      = f.natDegree + g.natDegree - (gcd f g).natDegree := by
  rw [rank_sylvester_eq_finrank_range f g f.natDegree g.natDegree le_rfl le_rfl]
  have hdim := LinearMap.finrank_range_add_finrank_ker
    (Polynomial.sylvesterMap f g (le_refl f.natDegree) (le_refl g.natDegree))
  rw [Module.finrank_prod, gsc_finrank_degreeLT, gsc_finrank_degreeLT,
    gsc_finrank_ker_sylvesterMap f g hf hg] at hdim
  omega

/-! ## Auxiliary facts -/

lemma gsc_gcd_zero_left (a : Polynomial ℝ) : (gcd 0 a).natDegree = a.natDegree := by
  rw [gcd_zero_left, Polynomial.natDegree_normalize]

lemma gsc_gcd_zero_right (a : Polynomial ℝ) : (gcd a 0).natDegree = a.natDegree := by
  rw [gcd_comm, gcd_zero_left, Polynomial.natDegree_normalize]

/-- Equal signs of two reals give equality of their vanishing. -/
lemma gsc_eq_zero_iff_of_sign_eq {a b : ℝ} (h : SignType.sign a = SignType.sign b) :
    a = 0 ↔ b = 0 := by
  rw [← sign_eq_zero_iff, h, sign_eq_zero_iff]

/-- If two polynomials of degree at most `D` have the same pattern of vanishing coefficients up to
index `D`, then one of them vanishes if and only if the other does. -/
lemma gsc_eq_zero_iff_of_coeff_eq_zero_iff {f g : Polynomial ℝ} {D : ℕ}
    (hf : f.natDegree ≤ D) (hg : g.natDegree ≤ D)
    (h : ∀ j, j ≤ D → (f.coeff j = 0 ↔ g.coeff j = 0)) : f = 0 ↔ g = 0 := by
  constructor
  · intro h0
    ext n
    by_cases hn : n ≤ D
    · exact (h n hn).mp (by rw [h0]; simp)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hg (not_le.mp hn))
  · intro h0
    ext n
    by_cases hn : n ≤ D
    · exact (h n hn).mpr (by rw [h0]; simp)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hf (not_le.mp hn))

/-! ## The main theorem -/

theorem gcd_spec_natDegree_const_on_C {m k : ℕ} (P : Fin k → MvPolynomial (Fin (m + 1)) ℝ) (D : ℕ)
    (hD : ∀ i : Fin k, (P i).degreeOf (Fin.last m) ≤ D)
    (C : Set (Fin m → ℝ))
    (hcoeff : ∀ i : Fin k, ∀ j : ℕ, j ≤ D → ∀ x ∈ C, ∀ x' ∈ C,
      SignType.sign ((Work.WilE4.spec (P i) x).coeff j)
        = SignType.sign ((Work.WilE4.spec (P i) x').coeff j))
    (hmin : ∀ i j : Fin k, ∀ a b : ℕ, a ≤ D → b ≤ D → ∀ l : ℕ, ∀ r c : Fin l → Fin (a + b),
      ∀ x ∈ C, ∀ x' ∈ C,
      SignType.sign (Matrix.det ((Polynomial.sylvester (Work.WilE4.spec (P i) x) (Work.WilE4.spec (P j) x) a b).submatrix r c))
        = SignType.sign (Matrix.det ((Polynomial.sylvester (Work.WilE4.spec (P i) x') (Work.WilE4.spec (P j) x') a b).submatrix r c)))
    (i j : Fin k) (x x' : Fin m → ℝ) (hx : x ∈ C) (hx' : x' ∈ C) :
    (gcd (Work.WilE4.spec (P i) x) (Work.WilE4.spec (P j) x)).natDegree
      = (gcd (Work.WilE4.spec (P i) x') (Work.WilE4.spec (P j) x')).natDegree := by
  -- The `natDegree` of every specialisation is constant on `C`.
  have hnd : ∀ i : Fin k, (spec (P i) x).natDegree = (spec (P i) x').natDegree :=
    fun i => natDegree_spec_const
      (fun i j hj y hy y' hy' => hcoeff i j (le_trans hj (hD i)) y hy y' hy') hx hx'
  -- A coefficient of index `≤ D` vanishes at `x` exactly when it vanishes at `x'`.
  have hzero : ∀ i : Fin k, ∀ j : ℕ, j ≤ D →
      ((spec (P i) x).coeff j = 0 ↔ (spec (P i) x').coeff j = 0) := by
    intro i j hj
    rw [← sign_eq_zero_iff, hcoeff i j hj x hx x' hx', sign_eq_zero_iff]
  have hdeg : ∀ i : Fin k, (spec (P i) x).natDegree ≤ D :=
    fun i => (natDegree_spec_le (P i) x).trans (hD i)
  have hdeg' : ∀ i : Fin k, (spec (P i) x').natDegree ≤ D :=
    fun i => (natDegree_spec_le (P i) x').trans (hD i)
  -- Hence a member vanishes at `x` exactly when it vanishes at `x'`.
  have hz : ∀ i : Fin k, ((spec (P i) x) = 0 ↔ (spec (P i) x') = 0) :=
    fun i => gsc_eq_zero_iff_of_coeff_eq_zero_iff (hdeg i) (hdeg' i) (hzero i)
  by_cases hFi : (spec (P i) x) = 0
  · -- `spec (P i)` vanishes identically on `C`: both sides equal `natDegree (spec (P j))`.
    have hFi' : (spec (P i) x') = 0 := (hz i).mp hFi
    rw [hFi, hFi', gsc_gcd_zero_left, gsc_gcd_zero_left]
    exact hnd j
  · have hFi' : (spec (P i) x') ≠ 0 := fun h => hFi ((hz i).mpr h)
    by_cases hGj : (spec (P j) x) = 0
    · have hGj' : (spec (P j) x') = 0 := (hz j).mp hGj
      rw [hGj, hGj', gsc_gcd_zero_right, gsc_gcd_zero_right]
      exact hnd i
    · -- Both members are nonzero: compare the ranks of the Sylvester matrices.
      have hGj' : (spec (P j) x') ≠ 0 := fun h => hGj ((hz j).mpr h)
      let M := (spec (P i) x).natDegree
      let N := (spec (P j) x).natDegree
      have hMle : M ≤ D := hdeg i
      have hNle : N ≤ D := hdeg j
      have hM' : M = (spec (P i) x').natDegree := hnd i
      have hN' : N = (spec (P j) x').natDegree := hnd j
      -- constancy of the ranks, from the constancy of all minors
      have hrank : (Polynomial.sylvester (spec (P i) x) (spec (P j) x) M N).rank
          = (Polynomial.sylvester (spec (P i) x') (spec (P j) x') M N).rank := by
        refine rank_eq_of_minors_det_eq_zero_iff ?_
        intro l r c
        exact gsc_eq_zero_iff_of_sign_eq (hmin i j M N hMle hNle l r c x hx x' hx')
      -- the rank formula turns rank equality into equality of gcd degrees
      have keyx : (gcd (spec (P i) x) (spec (P j) x)).natDegree
          = M + N - (Polynomial.sylvester (spec (P i) x) (spec (P j) x) M N).rank := by
        have h := gsc_rank_sylvester (spec (P i) x) (spec (P j) x) hFi hGj
        have hδ : (gcd (spec (P i) x) (spec (P j) x)).natDegree ≤ M + N :=
          (Polynomial.natDegree_le_of_dvd (gcd_dvd_left _ _) hFi).trans (Nat.le_add_right M N)
        have h' : (Polynomial.sylvester (spec (P i) x) (spec (P j) x) M N).rank
            = M + N - (gcd (spec (P i) x) (spec (P j) x)).natDegree := h
        omega
      have keyx' : (gcd (spec (P i) x') (spec (P j) x')).natDegree
          = M + N - (Polynomial.sylvester (spec (P i) x') (spec (P j) x') M N).rank := by
        have h := gsc_rank_sylvester (spec (P i) x') (spec (P j) x') hFi' hGj'
        rw [← hM', ← hN'] at h
        have hδ : (gcd (spec (P i) x') (spec (P j) x')).natDegree ≤ M + N := by
          refine (Polynomial.natDegree_le_of_dvd (gcd_dvd_left _ _) hFi').trans ?_
          rw [← hM']
          exact Nat.le_add_right M N
        omega
      rw [keyx, keyx', hrank]

end Work.WilE4.CAD
