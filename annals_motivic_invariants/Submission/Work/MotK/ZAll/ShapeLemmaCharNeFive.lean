import Mathlib
import Submission.Work.MotK.TGen.CruxAux
import Submission.Work.MotK.TGen.Gg_reducible_disc
import Submission.Work.Twist.chartDhom_eq_zero
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.MotK.ZAll

open MvPolynomial

variable {K : Type} [Field K]

/-!
# `Work.MotK.ZAll.ShapeLemmaCharNeFive`

The five-term binary quintic `f = a X₀⁵ + b X₀²X₁ + c X₀X₁³ + d X₁⁵ + e` over a field of
characteristic `≠ 5`, with `a,d,e ≠ 0`, is reducible only if `c² = 5 d b`.

The proof homogenises `f` to the ternary quintic
`Gg a d e b c = a x₀⁵ + d x₁⁵ + e x₂⁵ + b x₀²x₁x₂² + c x₀x₁³x₂` (`Work.MotK.TGen.Gg`), using
`Work.MotK.TGen.Gg_reducible_disc` (the public form of the crux `SdG5hCrux`), and the standard
fact that a factorisation of the dehomogenisation whose degrees add up to `5` lifts to a
factorisation of the homogenisation.

The homogenisation machinery (`D`, `homog` and their properties) is the new library content
here; the key point is that `D` is injective on polynomials which are homogeneous of a fixed
degree (`Work.Twist.chartDhom_eq_zero`), which turns "same dehomogenisation + same degree" into
"equal".
-/

/-! ## The dehomogenisation `K[x₀,x₁,x₂] →+* K[x₀,x₁]` -/

/-- Dehomogenisation at `x₂ = 1`: `x₀ ↦ x₀`, `x₁ ↦ x₁`, `x₂ ↦ 1`. -/
noncomputable def D : MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 2) K :=
  MvPolynomial.eval₂Hom (algebraMap K (MvPolynomial (Fin 2) K))
    (fun i : Fin 3 => ![MvPolynomial.X 0, MvPolynomial.X 1, 1] i)

lemma D_X_zero : D (MvPolynomial.X (0 : Fin 3)) = (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) := by
  simp [D]

lemma D_X_one : D (MvPolynomial.X (1 : Fin 3)) = (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) := by
  simp [D]

lemma D_X_two : D (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) K) = 1 := by
  simp [D]

lemma D_C (r : K) : D (MvPolynomial.C r) = MvPolynomial.C r := by
  simp only [D, MvPolynomial.eval₂Hom_C, MvPolynomial.algebraMap_eq]

/-- `D` fixes polynomials in the first two variables. -/
lemma D_rename_castSucc (q : MvPolynomial (Fin 2) K) :
    D (MvPolynomial.rename (Fin.castSucc : Fin 2 → Fin 3) q) = q := by
  induction q using MvPolynomial.induction_on with
  | C r =>
      rw [MvPolynomial.rename_C]
      exact D_C r
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
      have hXi : D (MvPolynomial.rename (Fin.castSucc : Fin 2 → Fin 3)
          (MvPolynomial.X i : MvPolynomial (Fin 2) K)) = MvPolynomial.X i := by
        fin_cases i <;>
          simp [D, MvPolynomial.rename_X, Fin.castSucc_zero, Fin.castSucc_one]
      simp only [map_mul, hp, hXi]

/-! ## Homogenisation of a binary polynomial -/

/-- `k`-homogenisation of a binary polynomial into the three variables `x₀,x₁,x₂`. -/
noncomputable def homog (k : ℕ) (p : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 3) K :=
  ∑ i ∈ Finset.range (k + 1),
    MvPolynomial.rename (Fin.castSucc : Fin 2 → Fin 3) (MvPolynomial.homogeneousComponent i p)
      * (MvPolynomial.X (2 : Fin 3)) ^ (k - i)

lemma homog_isHomogeneous (k : ℕ) (p : MvPolynomial (Fin 2) K) :
    (homog k p).IsHomogeneous k := by
  simp only [homog]
  refine MvPolynomial.IsHomogeneous.sum (Finset.range (k + 1)) _ k ?_
  intro i hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h1 : (MvPolynomial.rename (Fin.castSucc : Fin 2 → Fin 3)
      (MvPolynomial.homogeneousComponent i p)).IsHomogeneous i :=
    (MvPolynomial.homogeneousComponent_isHomogeneous i p).rename_isHomogeneous
  have h2 : ((MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) K) ^ (k - i)).IsHomogeneous
      (k - i) :=
    MvPolynomial.isHomogeneous_X_pow (2 : Fin 3) (k - i)
  have h3 := h1.mul h2
  rwa [show i + (k - i) = k by omega] at h3

/-- The homogenisation of `p` dehomogenises back to `p`. -/
lemma D_homog (k : ℕ) (p : MvPolynomial (Fin 2) K) (hp : p.totalDegree ≤ k) :
    D (homog k p) = p := by
  simp only [homog, map_sum]
  have hterm : ∀ i ∈ Finset.range (k + 1),
      D (MvPolynomial.rename (Fin.castSucc : Fin 2 → Fin 3)
            (MvPolynomial.homogeneousComponent i p)
          * (MvPolynomial.X (2 : Fin 3)) ^ (k - i)) = MvPolynomial.homogeneousComponent i p := by
    intro i hi
    simp only [map_mul, map_pow, D_rename_castSucc, D_X_two, one_pow, mul_one]
  rw [Finset.sum_congr rfl hterm]
  conv_rhs => rw [← MvPolynomial.sum_homogeneousComponent p]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro i hi
    rw [Finset.mem_range] at hi ⊢
    omega
  · intro i hi hni
    rw [Finset.mem_range] at hni
    exact MvPolynomial.homogeneousComponent_eq_zero i p (by omega)

lemma homog_ne_zero (k : ℕ) (p : MvPolynomial (Fin 2) K) (hp : p ≠ 0)
    (hk : p.totalDegree ≤ k) : homog k p ≠ 0 := by
  intro hz
  exact hp (by rw [← D_homog k p hk, hz, map_zero])

/-! ## `D` is injective on homogeneous polynomials of a fixed degree -/

/-- The permutation of the variables sending the homogenising variable `x₂` to the first
position, so that `D` becomes the `x₀ = 1` chart of `Work.Twist.chartDhom_eq_zero`. -/
private def tau : Fin 3 → Fin 3 := ![1, 2, 0]

private lemma tau_injective : Function.Injective tau := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [tau]

/-- The `x₀ = 1` chart substitution of `Work.Twist.chartDhom_eq_zero`. -/
private noncomputable def chartDhom : MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 2) K :=
  MvPolynomial.eval₂Hom (algebraMap K (MvPolynomial (Fin 2) K))
    (Fin.cases 1 (fun j : Fin 2 => MvPolynomial.X j))

/-- The `x₀ = 1` chart substitution composed with the variable permutation `tau` agrees with `D`. -/
private lemma chartDhom_rename_tau (x : MvPolynomial (Fin 3) K) :
    chartDhom (MvPolynomial.rename tau x) = D x := by
  induction x using MvPolynomial.induction_on with
  | C r => simp only [MvPolynomial.rename_C, chartDhom, D, MvPolynomial.eval₂Hom_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
      have hXi : chartDhom (MvPolynomial.rename tau (MvPolynomial.X i : MvPolynomial (Fin 3) K))
          = D (MvPolynomial.X i) := by
        fin_cases i <;>
          simp only [chartDhom, D, tau, MvPolynomial.rename_X, Matrix.cons_val_zero,
            Matrix.cons_val_succ, MvPolynomial.eval₂Hom_X'] <;>
          rfl
      simp only [map_mul, hp, hXi]

/-- If a polynomial which is homogeneous of degree `k` dehomogenises to `0`, it is `0`. -/
lemma eq_zero_of_isHomogeneous_D_eq_zero (k : ℕ) (x : MvPolynomial (Fin 3) K)
    (hx : x.IsHomogeneous k) (hD : D x = 0) : x = 0 := by
  have h1 : chartDhom (MvPolynomial.rename tau x) = 0 := by
    rw [chartDhom_rename_tau x, hD]
  have hx' : (MvPolynomial.rename tau x).IsHomogeneous k := hx.rename_isHomogeneous
  have h2 : MvPolynomial.rename tau x = 0 := Work.Twist.chartDhom_eq_zero K 2 hx' h1
  exact (MvPolynomial.rename_injective tau tau_injective) (by rw [h2, map_zero])

/-! ## Degree bookkeeping -/

/-- A unit of a polynomial ring over a nontrivial ring has total degree `0`. -/
lemma totalDegree_eq_zero_of_isUnit {σ : Type*} {p : MvPolynomial σ K} (hp : IsUnit p) :
    p.totalDegree = 0 := by
  obtain ⟨u, rfl⟩ := hp
  have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain
    (f := (u : MvPolynomial σ K)) (g := 1) ⟨↑u⁻¹, (Units.mul_inv u).symm⟩ one_ne_zero
  rw [MvPolynomial.totalDegree_one] at hle
  exact Nat.le_zero.mp hle

lemma isUnit_C_of_ne_zero {r : K} (hr : r ≠ 0) :
    IsUnit (MvPolynomial.C r : MvPolynomial (Fin 2) K) :=
  IsUnit.map (MvPolynomial.C : K →+* MvPolynomial (Fin 2) K) (isUnit_iff_ne_zero.mpr hr)

/-- A nonzero non-unit of a polynomial ring over a field has positive total degree. -/
lemma one_le_totalDegree_of_not_isUnit {p : MvPolynomial (Fin 2) K} (hp0 : p ≠ 0)
    (hpu : ¬ IsUnit p) : 1 ≤ p.totalDegree := by
  rcases Nat.eq_zero_or_pos p.totalDegree with h0 | hpos
  · exfalso
    have hpC : p = MvPolynomial.C (p.coeff 0) := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0
    have hc : p.coeff 0 ≠ 0 := by
      intro hc0
      exact hp0 (by rw [hpC, hc0, map_zero])
    exact hpu (by rw [hpC]; exact isUnit_C_of_ne_zero hc)
  · exact hpos

/-! ## The five-term binary quintic -/

/-- The five-term binary quintic `a x₀⁵ + b x₀²x₁ + c x₀x₁³ + d x₁⁵ + e`. -/
noncomputable def fiveTerm (a b c d e : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C a * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^ 5
    + MvPolynomial.C b * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^ 2 * MvPolynomial.X 1
    + MvPolynomial.C c * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
        * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^ 3
    + MvPolynomial.C d * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^ 5 + MvPolynomial.C e

lemma Gg_isHomogeneous (g1 g2 g3 g4 g5 : K) :
    (Work.MotK.TGen.Gg g1 g2 g3 g4 g5).IsHomogeneous 5 := by
  have t1 : (C g1 * (X (0 : Fin 3)) ^ 5 : MvPolynomial (Fin 3) K).IsHomogeneous 5 :=
    (isHomogeneous_C (Fin 3) g1).mul (isHomogeneous_X_pow (0 : Fin 3) 5)
  have t2 : (C g2 * (X (1 : Fin 3)) ^ 5 : MvPolynomial (Fin 3) K).IsHomogeneous 5 :=
    (isHomogeneous_C (Fin 3) g2).mul (isHomogeneous_X_pow (1 : Fin 3) 5)
  have t3 : (C g3 * (X (2 : Fin 3)) ^ 5 : MvPolynomial (Fin 3) K).IsHomogeneous 5 :=
    (isHomogeneous_C (Fin 3) g3).mul (isHomogeneous_X_pow (2 : Fin 3) 5)
  have t4 : (C g4 * ((X (0 : Fin 3)) ^ 2 * X 1 * (X 2) ^ 2) :
      MvPolynomial (Fin 3) K).IsHomogeneous 5 :=
    (((isHomogeneous_X_pow (0 : Fin 3) 2).mul (isHomogeneous_X K 1)).mul
      (isHomogeneous_X_pow (2 : Fin 3) 2)).C_mul g4
  have t5 : (C g5 * (X (0 : Fin 3) * (X 1) ^ 3 * X 2) :
      MvPolynomial (Fin 3) K).IsHomogeneous 5 :=
    (((isHomogeneous_X K 0).mul (isHomogeneous_X_pow (1 : Fin 3) 3)).mul
      (isHomogeneous_X K 2)).C_mul g5
  rw [Work.MotK.TGen.Gg]
  exact IsHomogeneous.add (IsHomogeneous.add (IsHomogeneous.add (IsHomogeneous.add t1 t2) t3) t4) t5

/-- The dehomogenisation of `Gg a d e b c` is `fiveTerm a b c d e`. -/
lemma D_Gg (a b c d e : K) :
    D (Work.MotK.TGen.Gg a d e b c) = fiveTerm a b c d e := by
  simp only [fiveTerm, Work.MotK.TGen.Gg]
  simp only [map_add, map_mul, map_pow, D_C, D_X_zero, D_X_one, D_X_two, one_pow]
  first | refl_ring1 | ring

/-- The five-term quintic has total degree `5` when `a ≠ 0`. -/
lemma fiveTerm_totalDegree (a b c d e : K) (ha : a ≠ 0) :
    (fiveTerm a b c d e).totalDegree = 5 := by
  set top : MvPolynomial (Fin 2) K :=
    MvPolynomial.C a * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^ 5
      + MvPolynomial.C d * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^ 5 with htop
  set rest : MvPolynomial (Fin 2) K :=
    MvPolynomial.C b * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^ 2
        * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K)
      + MvPolynomial.C c * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
          * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^ 3
      + MvPolynomial.C e with hrest
  have hdecomp : fiveTerm a b c d e = top + rest := by
    simp only [fiveTerm, htop, hrest]
    first | refl_ring1 | ring
  have htop_ne : top ≠ 0 := by
    intro hz
    have h1 : MvPolynomial.aeval (fun i : Fin 2 => ![(1 : K), 0] i) top = a := by
      rw [htop]
      simp only [map_add, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
      norm_num
    rw [hz, map_zero] at h1
    exact ha h1.symm
  have htop_hom : top.IsHomogeneous 5 := by
    rw [htop]
    exact (MvPolynomial.isHomogeneous_C_mul_X_pow a (0 : Fin 2) 5).add
      (MvPolynomial.isHomogeneous_C_mul_X_pow d (1 : Fin 2) 5)
  have htop_td : top.totalDegree = 5 := htop_hom.totalDegree htop_ne
  have hrest_td : rest.totalDegree ≤ 4 := by
    rw [hrest]
    have hb : (MvPolynomial.C b * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^ 2
        * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K)).totalDegree ≤ 4 := by
      have hb2 : (MvPolynomial.C b * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^ 2).totalDegree
          ≤ 2 := by
        have h1 := MvPolynomial.totalDegree_mul (MvPolynomial.C b)
          ((MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^ 2)
        rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X_pow] at h1
        omega
      have h1 := MvPolynomial.totalDegree_mul
        (MvPolynomial.C b * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^ 2)
        (MvPolynomial.X 1 : MvPolynomial (Fin 2) K)
      rw [MvPolynomial.totalDegree_X] at h1
      omega
    have hc : (MvPolynomial.C c * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
        * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^ 3).totalDegree ≤ 4 := by
      have hc2 : (MvPolynomial.C c * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)).totalDegree
          ≤ 1 := by
        have h1 := MvPolynomial.totalDegree_mul (MvPolynomial.C c)
          (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
        rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X] at h1
        omega
      have h1 := MvPolynomial.totalDegree_mul
        (MvPolynomial.C c * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K))
        ((MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^ 3)
      rw [MvPolynomial.totalDegree_X_pow] at h1
      omega
    have he : (MvPolynomial.C e : MvPolynomial (Fin 2) K).totalDegree ≤ 4 := by
      have h1 : (MvPolynomial.C e : MvPolynomial (Fin 2) K).totalDegree = 0 :=
        MvPolynomial.totalDegree_C e
      omega
    exact (MvPolynomial.totalDegree_add _ _).trans
      (max_le ((MvPolynomial.totalDegree_add _ _).trans (max_le hb hc)) he)
  have hstep : (top + rest).totalDegree = 5 := by
    rw [MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt (p := top) (q := rest) (by omega)]
    exact htop_td
  rw [hdecomp]
  exact hstep

/-! ## The reduction: a reducible five-term quintic gives a reducible `Gg` -/

lemma Gg_not_irreducible (a b c d e : K) (ha : a ≠ 0)
    (h : ¬ Irreducible (fiveTerm a b c d e)) :
    ¬ Irreducible (Work.MotK.TGen.Gg a d e b c) := by
  intro hG
  have hftd : (fiveTerm a b c d e).totalDegree = 5 := fiveTerm_totalDegree a b c d e ha
  have hf0 : fiveTerm a b c d e ≠ 0 := by
    intro h0
    rw [h0, MvPolynomial.totalDegree_zero] at hftd
    exact absurd hftd (by norm_num)
  have hfu : ¬ IsUnit (fiveTerm a b c d e) := by
    intro hu
    have h0 := totalDegree_eq_zero_of_isUnit hu
    rw [hftd] at h0
    exact absurd h0 (by norm_num)
  obtain ⟨g, hh, hgu, hhu, hfac⟩ := (irreducible_or_factor hfu).resolve_left h
  have hg0 : g ≠ 0 := fun h0 => hf0 (by rw [hfac, h0, zero_mul])
  have hh0 : hh ≠ 0 := fun h0 => hf0 (by rw [hfac, h0, mul_zero])
  have hmn : g.totalDegree + hh.totalDegree = 5 := by
    have h1 := MvPolynomial.totalDegree_mul_of_isDomain hg0 hh0
    rw [← hfac] at h1
    omega
  have hg1 : 1 ≤ g.totalDegree := one_le_totalDegree_of_not_isUnit hg0 hgu
  have hh1 : 1 ≤ hh.totalDegree := one_le_totalDegree_of_not_isUnit hh0 hhu
  have hkey : homog g.totalDegree g * homog hh.totalDegree hh
      = Work.MotK.TGen.Gg a d e b c := by
    refine sub_eq_zero.mp (eq_zero_of_isHomogeneous_D_eq_zero 5 _ ?_ ?_)
    · have hmul := (homog_isHomogeneous g.totalDegree g).mul
        (homog_isHomogeneous hh.totalDegree hh)
      rw [hmn] at hmul
      exact hmul.sub (Gg_isHomogeneous a d e b c)
    · rw [map_sub, map_mul, D_homog _ _ le_rfl, D_homog _ _ le_rfl, D_Gg, hfac, sub_self]
  have hnu1 : ¬ IsUnit (homog g.totalDegree g) := by
    intro hu
    have h0 := totalDegree_eq_zero_of_isUnit hu
    have htd : (homog g.totalDegree g).totalDegree = g.totalDegree :=
      (homog_isHomogeneous g.totalDegree g).totalDegree (homog_ne_zero _ g hg0 le_rfl)
    omega
  have hnu2 : ¬ IsUnit (homog hh.totalDegree hh) := by
    intro hu
    have h0 := totalDegree_eq_zero_of_isUnit hu
    have htd : (homog hh.totalDegree hh).totalDegree = hh.totalDegree :=
      (homog_isHomogeneous hh.totalDegree hh).totalDegree (homog_ne_zero _ hh hh0 le_rfl)
    omega
  rcases hG.isUnit_or_isUnit hkey.symm with hu | hu
  · exact hnu1 hu
  · exact hnu2 hu

/-! ## The main statement -/

/-- The five-term binary quintic `f = a X₀⁵ + b X₀²X₁ + c X₀X₁³ + d X₁⁵ + e` over a field of
characteristic `≠ 5`, with `a,d,e ≠ 0`, is reducible only if `c² = 5 d b`. -/
theorem ShapeLemmaCharNeFive (K : Type) [Field K] (h5 : (5 : K) ≠ 0) (a b c d e : K)
    (ha : a ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (h : ¬ Irreducible (MvPolynomial.C a * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^ 5
      + MvPolynomial.C b * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^ 2 * MvPolynomial.X 1
      + MvPolynomial.C c * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
          * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^ 3
      + MvPolynomial.C d * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^ 5 + MvPolynomial.C e)) :
    c ^ 2 = 5 * d * b := by
  have hk : ringChar K ≠ 5 := by
    intro hc
    have h : (ringChar K : K) = 0 := by rw [ringChar.spec]
    rw [hc] at h
    exact h5 h
  have h' : ¬ Irreducible (fiveTerm a b c d e) := h
  refine Work.MotK.TGen.Gg_reducible_disc (K := K) hk a d e b c ha hd he ?_
  exact Gg_not_irreducible a b c d e ha h'

end Work.MotK.ZAll
