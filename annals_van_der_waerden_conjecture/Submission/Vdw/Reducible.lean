import Mathlib
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Analysis.Polynomial.Norm
import Submission.Vdw.Counting
import Submission.Vdw.Structure
import Submission.Commons.Analysis.Asymptotics.isBigO_of_eventually_le
import Submission.Vdw.LinearFactor
import Submission.Vdw.Height

open vanDerWaerdenConjecture
open Function Polynomial Filter Asymptotics
open scoped BigOperators

set_option autoImplicit false

/-!
# The number of reducible polynomials in the box is O(H^(n-1))

This is the classical van der Waerden / Chela "intransitive" count: the
reducible monic integer polynomials of degree `n` with coefficients bounded by
`H` are `O(H^(n-1))` for `n ≥ 3`.

Strategy.  A reducible polynomial `p` has a monic factor `f` of degree
`k ≤ n/2` (choose the smaller of the two factors).  Write `Rₖ` for the box
polynomials admitting a monic factor of degree exactly `k` whose complementary
factor has degree `n-k` (`HasSmallFactor n H k`); then the reducible count is
at most the sum over `k = 1..n/2` of `#Rₖ`.

* `k = 1`: a monic degree-1 factor is `X - r`; either `r = 0` (then the
  constant term vanishes: `ZeroConst`) or `r ≠ 0` (`HasIntRoot`).  Both are
  `O(H^(n-1))` by `Submission.Vdw.LinearFactor`.

* `k ≥ 2`: `Rₖ` injects into the set of factor pairs `(f,g)` with
  `f · g` in the box (`PairSet`).  The height-product bound of
  `Submission.Vdw.Height` (`polyHeight_mul_le`) shows every such pair has
  `polyHeight f · polyHeight g ≤ Cₙₖ(H+1)`, and counting coefficient vectors
  of bounded height gives `#PairSet ≤ 3^n · [Cₙₖ(H+1)]^(n-k+1)` with
  `n-k+1 ≤ n-1` because `k ≥ 2`.  This is the whole point of the Mahler
  measure: pairs of factors cannot both have large coefficients.
-/

namespace Submission.Vdw

/-- Box polynomials admitting a monic factor of degree `k` whose cofactor has
degree `n-k`. -/
def HasSmallFactor (n H : ℕ) (k : ℕ) : Set ℤ[X] :=
  {p | p ∈ Box n H ∧ ∃ f : ℤ[X], f.Monic ∧ f.natDegree = k ∧
       ∃ g : ℤ[X], g.Monic ∧ g.natDegree = n - k ∧ f * g = p}

/-- Pairs of monic factors whose product lies in the box. -/
def PairSet (n H k : ℕ) : Set (ℤ[X] × ℤ[X]) :=
  {(fg : ℤ[X] × ℤ[X]) | fg.1.Monic ∧ fg.1.natDegree = k ∧ fg.2.Monic ∧
    fg.2.natDegree = n - k ∧ fg.1 * fg.2 ∈ Box n H}

/-- The box polynomials that are reducible. -/
def RedBox (n H : ℕ) : Set ℤ[X] :=
  {p | p ∈ Box n H ∧ Reducible p}

section Basic

/-- A monic linear polynomial is `X + c`. -/
lemma monic_linear_eq_X_add_C {f : ℤ[X]} (hf : f.Monic) (hd : f.natDegree = 1) :
    f = X + C (f.coeff 0) := by
  have hc1 : f.coeff 1 = 1 := by
    calc
      f.coeff 1 = f.coeff f.natDegree := by rw [hd]
      _ = f.leadingCoeff := Polynomial.coeff_natDegree
      _ = 1 := by simpa [Polynomial.Monic.def] using hf
  have hne : f ≠ 0 := Polynomial.Monic.ne_zero hf
  have hdeg : f.degree ≤ 1 := by
    rw [Polynomial.degree_eq_natDegree hne, hd]
    norm_num
  rw [eq_X_add_C_of_degree_le_one hdeg]
  simp [hc1]

/-- Every reducible box polynomial has a monic factor of degree `k ≤ n/2`. -/
lemma reducible_small_factor (n H : ℕ) {p : ℤ[X]} (hp : p ∈ Box n H)
    (hred : Reducible p) :
    ∃ k : ℕ, 1 ≤ k ∧ 2 * k ≤ n ∧ p ∈ HasSmallFactor n H k := by
  rcases hred with ⟨u, v, hum, hvm, hud, hvd, hprod⟩
  have hndp : p.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some hp.2.1
  have hnd_mul : (u * v).natDegree = u.natDegree + v.natDegree :=
    Polynomial.natDegree_mul (Polynomial.Monic.ne_zero hum) (Polynomial.Monic.ne_zero hvm)
  have hn_eq : u.natDegree + v.natDegree = n := by
    calc
      u.natDegree + v.natDegree = (u * v).natDegree := hnd_mul.symm
      _ = p.natDegree := by rw [hprod]
      _ = n := hndp
  by_cases hsmall : u.natDegree ≤ v.natDegree
  · refine ⟨u.natDegree, hud, ?_, hp, u, hum, rfl, v, hvm, ?_, hprod⟩
    · omega
    · omega
  · refine ⟨v.natDegree, hvd, ?_, hp, v, hvm, rfl, u, hum, ?_, ?_⟩
    · omega
    · omega
    · rw [mul_comm]
      exact hprod

/-- The height of a box polynomial is at most `H+1`. -/
lemma polyHeight_box_le_succ {p : ℤ[X]} {n H : ℕ} (hp : p ∈ Box n H) :
    polyHeight p ≤ H + 1 := by
  refine (polyHeight_le_iff p (H + 1)).mpr ?_
  intro i
  have hdeg : p.degree = n := hp.2.1
  have hne : p ≠ 0 := Polynomial.Monic.ne_zero hp.1
  have hnd : p.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some hdeg
  have hlc : p.leadingCoeff = 1 := by simpa [Polynomial.Monic.def] using hp.1
  by_cases hi : i < n
  · have hb : |p.coeff i| ≤ (H : ℤ) := hp.2.2 i hi
    have hb' : (p.coeff i).natAbs ≤ H := by
      rw [Int.abs_eq_natAbs] at hb
      exact_mod_cast hb
    omega
  · have hnle : n ≤ i := by omega
    rcases lt_or_eq_of_le hnle with hlt | heq
    · have hc : p.coeff i = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [hnd]
        exact hlt
      simp [hc]
    · have hc : p.coeff i = 1 := by
        rw [← heq]
        calc
          p.coeff n = p.coeff p.natDegree := by rw [hnd]
          _ = p.leadingCoeff := Polynomial.coeff_natDegree
          _ = 1 := hlc
      simp [hc]

/-- Every element of `HasSmallFactor n H 1` is either an `X`-multiple (zero
constant term) or has a nonzero integer root. -/
lemma hasSmallFactor_one_subset (n H : ℕ) (_hn : 1 ≤ n) :
    HasSmallFactor n H 1 ⊆ ZeroConst n H ∪ HasIntRoot n H := by
  intro p hp
  rcases hp with ⟨hbox, f, hfm, hfd, g, hgm, hgd, hprod⟩
  have hfeq : f = X + C (f.coeff 0) := monic_linear_eq_X_add_C hfm hfd
  by_cases hc0 : f.coeff 0 = 0
  · left
    refine ⟨hbox, ?_⟩
    calc
      p.coeff 0 = (f * g).coeff 0 := by rw [← hprod]
      _ = (X * g).coeff 0 := by
        have : f = X := by rw [hfeq, hc0]; simp
        rw [this]
      _ = 0 := by simp
  · right
    refine ⟨hbox, -(f.coeff 0), ?_, ?_⟩
    · intro hz
      have : f.coeff 0 = 0 := by omega
      exact hc0 this
    · -- (X - C (-c)) ∣ p with witness g
      refine ⟨g, ?_⟩
      have hleft : X - C (-(f.coeff 0)) = f := by
        simpa using hfeq.symm
      calc
        p = f * g := by rw [hprod]
        _ = (X - C (-(f.coeff 0))) * g := by
          exact congrArg (fun h : ℤ[X] => h * g) hleft.symm

/-- The degree-one part is bounded by the union of the two linear-factor
families. -/
lemma hasSmallFactor_one_card_le (n H : ℕ) (hn : 1 ≤ n) :
    (HasSmallFactor n H 1).ncard ≤
      (ZeroConst n H).ncard + (HasIntRoot n H).ncard := by
  have hsub := hasSmallFactor_one_subset n H hn
  have hfin : (ZeroConst n H ∪ HasIntRoot n H).Finite := by
    refine (box_finite n H).subset ?_
    intro p hp
    rcases hp with hz | hr
    · exact hz.1
    · exact hr.1
  calc
    (HasSmallFactor n H 1).ncard ≤ (ZeroConst n H ∪ HasIntRoot n H).ncard :=
      Set.ncard_le_ncard hsub hfin
    _ ≤ (ZeroConst n H).ncard + (HasIntRoot n H).ncard := Set.ncard_union_le _ _

end Basic

section Counting

/-- Monic degree-`k` polynomials of height at most `x`. -/
def HeightFactor (k x : ℕ) : Set ℤ[X] :=
  {f | f.Monic ∧ f.natDegree = k ∧ polyHeight f ≤ x}

/-- Monic degree-`k` polynomials of height at most `x` sit inside the `k`-box. -/
lemma heightFactor_subset_box (k x : ℕ) :
    HeightFactor k x ⊆ Box k x := by
  intro f hf
  rcases hf with ⟨hfmon, hfnd, hfh⟩
  have hne : f ≠ 0 := Polynomial.Monic.ne_zero hfmon
  refine ⟨hfmon, ?_, ?_⟩
  · rw [Polynomial.degree_eq_natDegree hne, hfnd]
  · intro i hi
    have hle : (f.coeff i).natAbs ≤ x := by
      exact (natAbs_coeff_le_polyHeight i).trans hfh
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hle

/-- The number of monic degree-`k` polynomials of height at most `x` is at most
`(2x+1)^k`. -/
lemma heightFactor_card_le (k x : ℕ) :
    (HeightFactor k x).ncard ≤ (2 * x + 1) ^ k := by
  calc
    (HeightFactor k x).ncard ≤ (Box k x).ncard :=
      Set.ncard_le_ncard (heightFactor_subset_box k x) (box_finite k x)
    _ = (2 * x + 1) ^ k := Box_ncard_eq k x

/-- Height product bound specialized to pairs of degrees `(k, n-k)`. -/
lemma pair_height_mul_le (n H k : ℕ) (hk : k ≤ n) {f g : ℤ[X]} (hf : f.Monic)
    (hg : g.Monic) (hfk : f.natDegree = k) (hgl : g.natDegree = n - k)
    (hbox : f * g ∈ Box n H) :
    polyHeight f * polyHeight g ≤
      ((n + 1) * (k.choose (k / 2)) * ((n - k).choose ((n - k) / 2))) * (H + 1) := by
  have hdegsum : f.natDegree + g.natDegree = n := by omega
  calc
    polyHeight f * polyHeight g
        ≤ (f.natDegree + g.natDegree + 1) * (f.natDegree.choose (f.natDegree / 2)) *
            (g.natDegree.choose (g.natDegree / 2)) * polyHeight (f * g) :=
              polyHeight_mul_le f g hf hg
    _ = (n + 1) * (k.choose (k / 2)) * ((n - k).choose ((n - k) / 2)) * polyHeight (f * g) := by
      rw [hdegsum, hfk, hgl]
    _ ≤ ((n + 1) * (k.choose (k / 2)) * ((n - k).choose ((n - k) / 2))) * (H + 1) := by
      exact Nat.mul_le_mul_left _ (polyHeight_box_le_succ hbox)

/-- In every pair with product in the box, both factors have bounded height:
at most `(n+1)·B(k)·B(n-k)·(H+1)`. -/
lemma pair_height_le (n H k : ℕ) (hk : k ≤ n) {f g : ℤ[X]} (hf : f.Monic) (hg : g.Monic)
    (hfk : f.natDegree = k) (hgl : g.natDegree = n - k) (hbox : f * g ∈ Box n H) :
    polyHeight f ≤ (n + 1) * (k.choose (k / 2)) * ((n - k).choose ((n - k) / 2)) * (H + 1) ∧
    polyHeight g ≤ (n + 1) * (k.choose (k / 2)) * ((n - k).choose ((n - k) / 2)) * (H + 1) := by
  have hb := pair_height_mul_le n H k hk hf hg hfk hgl hbox
  have h1 : 1 ≤ polyHeight f := one_le_polyHeight_of_Monic hf
  have h2 : 1 ≤ polyHeight g := one_le_polyHeight_of_Monic hg
  have hfg_le_f : polyHeight f ≤ polyHeight f * polyHeight g := by
    calc
      polyHeight f = polyHeight f * 1 := by rw [mul_one]
      _ ≤ polyHeight f * polyHeight g := Nat.mul_le_mul_left _ h2
  have hfg_le_g : polyHeight g ≤ polyHeight f * polyHeight g := by
    calc
      polyHeight g = 1 * polyHeight g := by rw [one_mul]
      _ ≤ polyHeight f * polyHeight g := Nat.mul_le_mul_right _ h1
  constructor
  · exact hfg_le_f.trans hb
  · exact hfg_le_g.trans hb

/-- The pair set is finite. -/
lemma pairSet_finite (n H k : ℕ) (hk : k ≤ n) : (PairSet n H k).Finite := by
  let C : ℕ := (n + 1) * (k.choose (k / 2)) * ((n - k).choose ((n - k) / 2))
  let M : ℕ := C * (H + 1)
  have hsub : PairSet n H k ⊆
      {f | f.Monic ∧ f.natDegree = k ∧ polyHeight f ≤ M} ×ˢ
        {g | g.Monic ∧ g.natDegree = n - k ∧ polyHeight g ≤ M} := by
    intro x hx
    rcases hx with ⟨hfm, hfk, hgm, hgl, hbox⟩
    have hle := pair_height_le n H k hk hfm hgm hfk hgl hbox
    have hb1 : polyHeight x.1 ≤ M := by
      have : polyHeight x.1 ≤ C * (H + 1) := hle.1
      simpa [M] using this
    have hb2 : polyHeight x.2 ≤ M := by
      have : polyHeight x.2 ≤ C * (H + 1) := hle.2
      simpa [M] using this
    exact ⟨⟨hfm, hfk, hb1⟩, ⟨hgm, hgl, hb2⟩⟩
  refine (Set.Finite.prod
      ((box_finite k M).subset ?_) ((box_finite (n - k) M).subset ?_)).subset hsub
  · intro f hf
    exact heightFactor_subset_box k M hf
  · intro g hg
    exact heightFactor_subset_box (n - k) M hg

/-- Every element of `HasSmallFactor n H k` comes from a pair in `PairSet n H k`. -/
lemma hasSmallFactor_card_le_pairSet (n H k : ℕ) (hk : k ≤ n) :
    (HasSmallFactor n H k).ncard ≤ (PairSet n H k).ncard := by
  have hsub : HasSmallFactor n H k ⊆ (fun x : ℤ[X] × ℤ[X] => x.1 * x.2) '' PairSet n H k := by
    intro p hp
    rcases hp with ⟨hbox, f, hfm, hfk, g, hgm, hgl, hprod⟩
    refine ⟨(f, g), ?_, hprod⟩
    · refine ⟨hfm, hfk, hgm, hgl, ?_⟩
      change f * g ∈ Box n H
      rwa [hprod]
  have hfin : ((fun x : ℤ[X] × ℤ[X] => x.1 * x.2) '' PairSet n H k).Finite := by
    refine (pairSet_finite n H k hk).image _
  calc
    (HasSmallFactor n H k).ncard ≤
        ((fun x : ℤ[X] × ℤ[X] => x.1 * x.2) '' PairSet n H k).ncard :=
          Set.ncard_le_ncard hsub hfin
    _ ≤ (PairSet n H k).ncard := Set.ncard_image_le (pairSet_finite n H k hk)

end Counting


section PairCounting

/-- The height bound for factor pairs with degrees `(k, n-k)`: both factors
have height at most `PairBound n k H`. -/
def PairBound (n k H : ℕ) : ℕ :=
  ((n + 1) * (k.choose (k / 2)) * ((n - k).choose ((n - k) / 2))) * (H + 1)

/-- Height product bound in terms of `PairBound`. -/
lemma pair_height_mul_le_PB (n H k : ℕ) (hk : k ≤ n) {f g : ℤ[X]} (hf : f.Monic)
    (hg : g.Monic) (hfk : f.natDegree = k) (hgl : g.natDegree = n - k)
    (hbox : f * g ∈ Box n H) :
    polyHeight f * polyHeight g ≤ PairBound n k H := by
  simpa [PairBound] using pair_height_mul_le n H k hk hf hg hfk hgl hbox

/-- Both factors in a pair have height at most `PairBound n k H`. -/
lemma pair_height_le_PB (n H k : ℕ) (hk : k ≤ n) {f g : ℤ[X]} (hf : f.Monic)
    (hg : g.Monic) (hfk : f.natDegree = k) (hgl : g.natDegree = n - k)
    (hbox : f * g ∈ Box n H) :
    polyHeight f ≤ PairBound n k H ∧ polyHeight g ≤ PairBound n k H := by
  have hb := pair_height_mul_le_PB n H k hk hf hg hfk hgl hbox
  have h1 : 1 ≤ polyHeight f := one_le_polyHeight_of_Monic hf
  have h2 : 1 ≤ polyHeight g := one_le_polyHeight_of_Monic hg
  have hfg_le_f : polyHeight f ≤ polyHeight f * polyHeight g := by
    calc
      polyHeight f = polyHeight f * 1 := by rw [mul_one]
      _ ≤ polyHeight f * polyHeight g := Nat.mul_le_mul_left _ h2
  have hfg_le_g : polyHeight g ≤ polyHeight f * polyHeight g := by
    calc
      polyHeight g = 1 * polyHeight g := by rw [one_mul]
      _ ≤ polyHeight f * polyHeight g := Nat.mul_le_mul_right _ h1
  constructor
  · exact hfg_le_f.trans hb
  · exact hfg_le_g.trans hb

/-- The bound is positive. -/
lemma pairBound_pos (n k H : ℕ) : 1 ≤ PairBound n k H := by
  dsimp [PairBound]
  have hc1 : 1 ≤ k.choose (k / 2) := Nat.choose_pos (by omega)
  have hc2 : 1 ≤ (n - k).choose ((n - k) / 2) := Nat.choose_pos (by omega)
  have hC : 1 ≤ (n + 1) * (k.choose (k / 2)) * ((n - k).choose ((n - k) / 2)) := by
    calc
      1 = 1 * 1 * 1 := by norm_num
      _ ≤ (n + 1) * (k.choose (k / 2)) * ((n - k).choose ((n - k) / 2)) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) hc1) hc2
  calc
    1 ≤ (n + 1) * (k.choose (k / 2)) * ((n - k).choose ((n - k) / 2)) := hC
    _ ≤ ((n + 1) * (k.choose (k / 2)) * ((n - k).choose ((n - k) / 2))) * (H + 1) := by
      have hle : ((n + 1) * (k.choose (k / 2)) * ((n - k).choose ((n - k) / 2))) * 1 ≤
          ((n + 1) * (k.choose (k / 2)) * ((n - k).choose ((n - k) / 2))) * (H + 1) :=
            Nat.mul_le_mul_left _ (by omega : 1 ≤ H + 1)
      simpa using hle

/-- The `a`-fibre of the pair set (pairs whose first factor has height `a`) is
bounded by the product of the two height counts. -/
lemma pairSet_fiber_card_le (n H k a : ℕ) (hk : k ≤ n) :
    ({x : ℤ[X] × ℤ[X] | x ∈ PairSet n H k ∧ polyHeight x.1 = a}).ncard ≤
      (2 * a + 1) ^ k * (2 * (PairBound n k H / a) + 1) ^ (n - k) := by
  classical
  by_cases ha : 1 ≤ a
  · let M : ℕ := PairBound n k H
    have hsub : {x | x ∈ PairSet n H k ∧ polyHeight x.1 = a} ⊆
        HeightFactor k a ×ˢ HeightFactor (n - k) (M / a) := by
      intro x hx
      rcases hx with ⟨hxP, hxa⟩
      rcases hxP with ⟨hfm, hfk, hgm, hgl, hbox⟩
      have hle := pair_height_mul_le_PB n H k hk hfm hgm hfk hgl hbox
      have hdiv : polyHeight x.2 ≤ M / a := by
        have hab : polyHeight x.1 * polyHeight x.2 ≤ M := by
          simpa [M] using hle
        have hamul : a * polyHeight x.2 ≤ M := by
          rw [hxa] at hab
          exact hab
        have hpos : 0 < a := by omega
        have : polyHeight x.2 * a ≤ M := by
          rwa [mul_comm] at hamul
        exact (Nat.le_div_iff_mul_le hpos).mpr this
      refine ⟨⟨hfm, hfk, ?_⟩, ⟨hgm, hgl, hdiv⟩⟩
      rw [hxa]
    have hfin1 : (HeightFactor k a).Finite := (box_finite k a).subset (heightFactor_subset_box k a)
    have hfin2 : (HeightFactor (n - k) (M / a)).Finite :=
      (box_finite (n - k) (M / a)).subset (heightFactor_subset_box (n - k) (M / a))
    calc
      ({x | x ∈ PairSet n H k ∧ polyHeight x.1 = a}).ncard
          ≤ (HeightFactor k a ×ˢ HeightFactor (n - k) (M / a)).ncard :=
            Set.ncard_le_ncard hsub (Set.Finite.prod hfin1 hfin2)
      _ = (HeightFactor k a).ncard * (HeightFactor (n - k) (M / a)).ncard := Set.ncard_prod
      _ ≤ (2 * a + 1) ^ k * (2 * (M / a) + 1) ^ (n - k) := by
        exact Nat.mul_le_mul (heightFactor_card_le k a) (heightFactor_card_le (n - k) (M / a))
      _ = (2 * a + 1) ^ k * (2 * (PairBound n k H / a) + 1) ^ (n - k) := by
        simp [M]
  · -- a = 0: no monic polynomial has height 0, so the fibre is empty
    have hzero : ∀ x : ℤ[X] × ℤ[X], ¬ (x ∈ PairSet n H k ∧ polyHeight x.1 = a) := by
      intro x hx
      rcases hx with ⟨hxP, hxa⟩
      rcases hxP with ⟨hfm, _hfk, _hgm, _hgl, _hbox⟩
      have hpos : 1 ≤ polyHeight x.1 := one_le_polyHeight_of_Monic hfm
      omega
    have hempty : {x : ℤ[X] × ℤ[X] | x ∈ PairSet n H k ∧ polyHeight x.1 = a} = ∅ := by
      ext x
      simp [hzero x]
    rw [hempty]
    simp

/-- The pair set splits over the possible heights `a = 1..PairBound`, and each
fibre is small; so the pair set is bounded by a single sum. -/
lemma pairSet_card_le_sum (n H k : ℕ) (hk : k ≤ n) :
    (PairSet n H k).ncard ≤
      ∑ a ∈ Finset.Icc 1 (PairBound n k H),
        (2 * a + 1) ^ k * (2 * (PairBound n k H / a) + 1) ^ (n - k) := by
  classical
  let M : ℕ := PairBound n k H
  let fiber : ℕ → Set (ℤ[X] × ℤ[X]) :=
    fun a => {x : ℤ[X] × ℤ[X] | x ∈ PairSet n H k ∧ polyHeight x.1 = a}
  have hcov : PairSet n H k = {x : ℤ[X] × ℤ[X] | ∃ a ∈ Finset.Icc 1 M, x ∈ fiber a} := by
    ext x
    constructor
    · intro hx
      have hxin : x ∈ PairSet n H k := hx
      rcases hx with ⟨hfm, hfk, hgm, hgl, hbox⟩
      refine ⟨polyHeight x.1, ?_, ⟨hxin, rfl⟩⟩
      rw [Finset.mem_Icc]
      constructor
      · exact one_le_polyHeight_of_Monic hfm
      · have hle := pair_height_le_PB n H k hk hfm hgm hfk hgl hbox
        have hb1 : polyHeight x.1 ≤ M := by simpa [M] using hle.1
        exact hb1
    · intro hx
      rcases hx with ⟨a, _ha, hmem⟩
      dsimp [fiber] at hmem
      exact hmem.1
  calc
    (PairSet n H k).ncard
        = {x : ℤ[X] × ℤ[X] | ∃ a ∈ Finset.Icc 1 M, x ∈ fiber a}.ncard := by rw [hcov]
    _ ≤ ∑ a ∈ Finset.Icc 1 M, (fiber a).ncard := ncard_biUnion_finset_le (Finset.Icc 1 M) fiber
    _ ≤ ∑ a ∈ Finset.Icc 1 M,
          (2 * a + 1) ^ k * (2 * (PairBound n k H / a) + 1) ^ (n - k) := by
        apply Finset.sum_le_sum
        intro a ha
        have hfib := pairSet_fiber_card_le n H k a hk
        simpa [fiber, M] using hfib
    _ = ∑ a ∈ Finset.Icc 1 (PairBound n k H),
          (2 * a + 1) ^ k * (2 * (PairBound n k H / a) + 1) ^ (n - k) := by
        simp [M]

/-- Pure counting bound: `Σ_{a=1}^M (2a+1)^k (2⌊M/a⌋+1)^l ≤ 3^(k+l) M^(l+1)`
when `k ≤ l` and `M ≥ 1`. -/
lemma pairSum_le (k l M : ℕ) (_hk1 : 1 ≤ k) (hkl : k ≤ l) (_hM1 : 1 ≤ M) :
    (∑ a ∈ Finset.Icc 1 M, (2 * a + 1) ^ k * (2 * (M / a) + 1) ^ l) ≤
      3 ^ (k + l) * M ^ (l + 1) := by
  have hterm : ∀ a ∈ Finset.Icc 1 M,
      (2 * a + 1) ^ k * (2 * (M / a) + 1) ^ l ≤ 3 ^ (k + l) * M ^ l := by
    intro a ha
    rcases Finset.mem_Icc.mp ha with ⟨ha1, haM⟩
    have hc1 : 2 * a + 1 ≤ 3 * a := by omega
    have hMd : 1 ≤ M / a := by
      exact (Nat.le_div_iff_mul_le (by omega : 0 < a)).2 (by rw [one_mul]; exact haM)
    have hc2 : 2 * (M / a) + 1 ≤ 3 * (M / a) := by omega
    have h3 : (2 * a + 1) ^ k ≤ (3 * a) ^ k := pow_le_pow_left₀ (by omega) hc1 k
    have h4 : (2 * (M / a) + 1) ^ l ≤ (3 * (M / a)) ^ l := pow_le_pow_left₀ (by omega) hc2 l
    have hmul : (2 * a + 1) ^ k * (2 * (M / a) + 1) ^ l ≤
        (3 * a) ^ k * (3 * (M / a)) ^ l := Nat.mul_le_mul h3 h4
    have hadv : a * (M / a) ≤ M := by
      rw [mul_comm]
      exact Nat.div_mul_le_self M a
    have hpow : (a * (M / a)) ^ l ≤ M ^ l := pow_le_pow_left₀ (Nat.zero_le _) hadv l
    have hdiv_l : a ^ l * (M / a) ^ l ≤ M ^ l := by
      simpa [mul_pow] using hpow
    have ha_k_le : a ^ k ≤ a ^ l := pow_le_pow_right₀ ha1 hkl
    have hmain : (3 * a) ^ k * (3 * (M / a)) ^ l ≤ 3 ^ (k + l) * M ^ l := by
      calc
        (3 * a) ^ k * (3 * (M / a)) ^ l = 3 ^ k * a ^ k * (3 ^ l * (M / a) ^ l) := by simp [mul_pow]
        _ = 3 ^ (k + l) * (a ^ k * (M / a) ^ l) := by
          rw [pow_add]
          ring
        _ ≤ 3 ^ (k + l) * (a ^ l * (M / a) ^ l) := by
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ ha_k_le)
        _ ≤ 3 ^ (k + l) * M ^ l := Nat.mul_le_mul_left _ hdiv_l
    exact hmul.trans hmain
  calc
    (∑ a ∈ Finset.Icc 1 M, (2 * a + 1) ^ k * (2 * (M / a) + 1) ^ l)
        ≤ ∑ a ∈ Finset.Icc 1 M, 3 ^ (k + l) * M ^ l := Finset.sum_le_sum hterm
    _ = (Finset.Icc 1 M).card * (3 ^ (k + l) * M ^ l) := by
      rw [Finset.sum_const]
      simp
    _ = 3 ^ (k + l) * M ^ l * M := by
      rw [show (Finset.Icc 1 M).card = M by simp]
      ring
    _ = 3 ^ (k + l) * M ^ (l + 1) := by
      rw [pow_succ]
      ring

/-- For degrees `k ≥ 2` (with `k ≤ n-k`), the number of pairs is `O(H^(n-1))`:
`#PairSet ≤ 3^n · PairBound^(n-1)`. -/
lemma pairSet_card_le_pow (n H k : ℕ) (hk2 : 2 ≤ k) (hkle : k ≤ n - k) :
    (PairSet n H k).ncard ≤ 3 ^ n * (PairBound n k H) ^ (n - 1) := by
  have hkn : k ≤ n := by omega
  have hk1 : 1 ≤ k := by omega
  let M : ℕ := PairBound n k H
  have hM1 : 1 ≤ M := pairBound_pos n k H
  have hsum := pairSet_card_le_sum n H k hkn
  have hps := pairSum_le k (n - k) M hk1 hkle hM1
  have hpowb : (PairBound n k H) ^ (n - k + 1) ≤ (PairBound n k H) ^ (n - 1) := by
    apply pow_le_pow_right₀ (pairBound_pos n k H)
    omega
  have hkadd : k + (n - k) = n := by omega
  calc
    (PairSet n H k).ncard ≤
        ∑ a ∈ Finset.Icc 1 (PairBound n k H),
          (2 * a + 1) ^ k * (2 * (PairBound n k H / a) + 1) ^ (n - k) := hsum
    _ ≤ 3 ^ (k + (n - k)) * M ^ ((n - k) + 1) := by
      simpa [M] using hps
    _ = 3 ^ n * M ^ (n - k + 1) := by
      rw [hkadd]
    _ ≤ 3 ^ n * (PairBound n k H) ^ (n - 1) := by
      dsimp [M]
      exact Nat.mul_le_mul_left _ hpowb

end PairCounting


section MainTheorem

/-- The reducible box polynomials split according to the degree `k` of the
smaller monic factor. -/
lemma redBox_subset_union (n H : ℕ) :
    RedBox n H ⊆ {p : ℤ[X] | ∃ k ∈ Finset.Icc 1 (n / 2), p ∈ HasSmallFactor n H k} := by
  intro p hp
  rcases hp with ⟨hbox, hred⟩
  rcases (reducible_small_factor n H hbox hred) with ⟨k, hk1, hk2, hmem⟩
  refine ⟨k, ?_, hmem⟩
  rw [Finset.mem_Icc]
  constructor
  · exact hk1
  · omega

/-- The reducible count is at most the sum of the small-factor counts. -/
lemma redBox_card_le_sum (n H : ℕ) :
    (RedBox n H).ncard ≤ ∑ k ∈ Finset.Icc 1 (n / 2), (HasSmallFactor n H k).ncard := by
  let U : ℕ → Set ℤ[X] := fun k => HasSmallFactor n H k
  have hfin : ({p : ℤ[X] | ∃ k ∈ Finset.Icc 1 (n / 2), p ∈ U k}).Finite := by
    refine (box_finite n H).subset ?_
    intro p hp
    rcases hp with ⟨k, _hk, hmem⟩
    exact hmem.1
  calc
    (RedBox n H).ncard ≤ {p : ℤ[X] | ∃ k ∈ Finset.Icc 1 (n / 2), p ∈ U k}.ncard :=
      Set.ncard_le_ncard (redBox_subset_union n H) hfin
    _ ≤ ∑ k ∈ Finset.Icc 1 (n / 2), (U k).ncard :=
      ncard_biUnion_finset_le (Finset.Icc 1 (n / 2)) U
    _ = ∑ k ∈ Finset.Icc 1 (n / 2), (HasSmallFactor n H k).ncard := rfl

/-- The `k = 1` part: box polynomials with a monic linear factor are
`O(H^(n-1))`. -/
lemma hasSmallFactor_one_pointwise (n H : ℕ) (hn3 : 3 ≤ n) (hH : 1 ≤ H) :
    (HasSmallFactor n H 1).ncard ≤
      (3 ^ (n - 1) + 3 ^ (n - 1) + 4 * (3 * n) ^ (n - 1)) * H ^ (n - 1) := by
  have hn1 : 1 ≤ n := by omega
  have h1 := hasSmallFactor_one_card_le n H hn1
  have hzc : (ZeroConst n H).ncard ≤ 3 ^ (n - 1) * H ^ (n - 1) := by
    have heq : (ZeroConst n H).ncard = (2 * H + 1) ^ (n - 1) := ZeroConst_ncard n H hn1
    calc
      (ZeroConst n H).ncard = (2 * H + 1) ^ (n - 1) := heq
      _ ≤ (3 * H) ^ (n - 1) := by
        exact Nat.pow_le_pow_left (by omega : 2 * H + 1 ≤ 3 * H) (n - 1)
      _ = 3 ^ (n - 1) * H ^ (n - 1) := by rw [mul_pow]
  have hhi_real := hasIntRoot_real_bound n H hn3 hH
  have hhi : (HasIntRoot n H).ncard ≤ (3 ^ (n - 1) + 4 * (3 * n) ^ (n - 1)) * H ^ (n - 1) := by
    have hhi2 : ((HasIntRoot n H).ncard : ℝ) ≤
        (((3 ^ (n - 1) + 4 * (3 * n) ^ (n - 1)) * H ^ (n - 1) : ℕ) : ℝ) := by
      simpa [Nat.cast_pow] using hhi_real
    exact_mod_cast hhi2
  calc
    (HasSmallFactor n H 1).ncard ≤ (ZeroConst n H).ncard + (HasIntRoot n H).ncard := h1
    _ ≤ 3 ^ (n - 1) * H ^ (n - 1) +
        (3 ^ (n - 1) + 4 * (3 * n) ^ (n - 1)) * H ^ (n - 1) := by
      exact Nat.add_le_add hzc hhi
    _ = (3 ^ (n - 1) + 3 ^ (n - 1) + 4 * (3 * n) ^ (n - 1)) * H ^ (n - 1) := by ring

/-- A bound for the central binomial-type factor of a degree `≤ n` monic
polynomial: `k.choose (k/2) ≤ n^n` for `k ≤ n`. -/
lemma choose_halves_le_pow_nat {k n : ℕ} (hk : k ≤ n) (hn : 1 ≤ n) :
    k.choose (k / 2) ≤ n ^ n := by
  by_cases hk0 : k = 0
  · simp [hk0]
    calc
      1 = 1 ^ n := by simp
      _ ≤ n ^ n := by
        exact Nat.pow_le_pow_left (by omega : 1 ≤ n) n
  · have hk1 : 1 ≤ k := by omega
    calc
      k.choose (k / 2) ≤ k ^ (k / 2) := Nat.choose_le_pow k (k / 2)
      _ ≤ k ^ k := pow_le_pow_right₀ hk1 (by omega)
      _ ≤ k ^ n := pow_le_pow_right₀ hk1 hk
      _ ≤ n ^ n := Nat.pow_le_pow_left (by omega : k ≤ n) n

/-- The pair bound for degree `k` is at most `(n+1)·n^(2n)·(H+1)`. -/
lemma pairBound_le_Cpair (n k H : ℕ) (hkn : k ≤ n) (hn : 1 ≤ n) :
    PairBound n k H ≤ (n + 1) * n ^ (2 * n) * (H + 1) := by
  have hb1 : k.choose (k / 2) ≤ n ^ n := choose_halves_le_pow_nat hkn hn
  have hnk : n - k ≤ n := by omega
  have hb2 : (n - k).choose ((n - k) / 2) ≤ n ^ n := choose_halves_le_pow_nat hnk hn
  dsimp [PairBound]
  calc
    ((n + 1) * (k.choose (k / 2)) * ((n - k).choose ((n - k) / 2))) * (H + 1)
        ≤ ((n + 1) * (n ^ n) * (n ^ n)) * (H + 1) := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ hb1) hb2)
    _ = (n + 1) * (n ^ n * n ^ n) * (H + 1) := by ring
    _ = (n + 1) * n ^ (n + n) * (H + 1) := by
      rw [pow_add]
    _ = (n + 1) * n ^ (2 * n) * (H + 1) := by
      congr 1
      ring

/-- The `k ≥ 2` part: for degrees `2 ≤ k ≤ n/2`, box polynomials with a monic
factor of degree `k` are `O(H^(n-1))`. -/
lemma hasSmallFactor_large_pointwise (n H : ℕ) (hn3 : 3 ≤ n) (hH : 1 ≤ H) {k : ℕ}
    (hk2 : 2 ≤ k) (hk : k ≤ n / 2) :
    (HasSmallFactor n H k).ncard ≤
      3 ^ n * (((n + 1) * n ^ (2 * n)) ^ (n - 1)) * 2 ^ (n - 1) * H ^ (n - 1) := by
  have hn1 : 1 ≤ n := by omega
  have hkn : k ≤ n := by omega
  have hkle : k ≤ n - k := by omega
  have h1 := hasSmallFactor_card_le_pairSet n H k hkn
  have hpf := pairSet_card_le_pow n H k hk2 hkle
  have hpb : PairBound n k H ≤ (n + 1) * n ^ (2 * n) * (H + 1) := pairBound_le_Cpair n k H hkn hn1
  have hpbpow : (PairBound n k H) ^ (n - 1) ≤ ((n + 1) * n ^ (2 * n) * (H + 1)) ^ (n - 1) :=
    Nat.pow_le_pow_left hpb (n - 1)
  have hHle : H + 1 ≤ 2 * H := by omega
  calc
    (HasSmallFactor n H k).ncard ≤ (PairSet n H k).ncard := h1
    _ ≤ 3 ^ n * (PairBound n k H) ^ (n - 1) := hpf
    _ ≤ 3 ^ n * (((n + 1) * n ^ (2 * n)) * (H + 1)) ^ (n - 1) := by
      exact Nat.mul_le_mul_left (3 ^ n) hpbpow
    _ = 3 ^ n * (((n + 1) * n ^ (2 * n)) ^ (n - 1)) * (H + 1) ^ (n - 1) := by
      rw [mul_pow]
      ring
    _ ≤ 3 ^ n * (((n + 1) * n ^ (2 * n)) ^ (n - 1)) * (2 * H) ^ (n - 1) := by
      exact Nat.mul_le_mul_left (3 ^ n * ((n + 1) * n ^ (2 * n)) ^ (n - 1))
        (Nat.pow_le_pow_left hHle (n - 1))
    _ = 3 ^ n * (((n + 1) * n ^ (2 * n)) ^ (n - 1)) * 2 ^ (n - 1) * H ^ (n - 1) := by
      rw [mul_pow]
      ring

/-- The global counting constant for the reducible polynomials. -/
def RedBoxConst (n : ℕ) : ℕ :=
  (n / 2) * ((3 ^ (n - 1) + 3 ^ (n - 1) + 4 * (3 * n) ^ (n - 1)) +
    3 ^ n * (((n + 1) * n ^ (2 * n)) ^ (n - 1)) * 2 ^ (n - 1))

/-- **Pointwise reducible bound.**  For `n ≥ 3` and `H ≥ 1`, the number of
reducible monic degree-`n` polynomials in the box is at most
`RedBoxConst n · H^(n-1)`. -/
theorem redBox_card_pointwise (n H : ℕ) (hn3 : 3 ≤ n) (hH : 1 ≤ H) :
    (RedBox n H).ncard ≤ RedBoxConst n * H ^ (n - 1) := by
  have hn1 : 1 ≤ n := by omega
  have hsum := redBox_card_le_sum n H
  let c1 : ℕ := 3 ^ (n - 1) + 3 ^ (n - 1) + 4 * (3 * n) ^ (n - 1)
  let ck : ℕ := 3 ^ n * (((n + 1) * n ^ (2 * n)) ^ (n - 1)) * 2 ^ (n - 1)
  have hterm : ∀ k ∈ Finset.Icc 1 (n / 2),
      (HasSmallFactor n H k).ncard ≤ (c1 + ck) * H ^ (n - 1) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rcases hk with ⟨hk1, hkm⟩
    by_cases hk1c : k = 1
    · have hb := hasSmallFactor_one_pointwise n H hn3 hH
      have hle : c1 ≤ c1 + ck := Nat.le_add_right c1 ck
      calc
        (HasSmallFactor n H k).ncard ≤ c1 * H ^ (n - 1) := by simpa [c1, hk1c] using hb
        _ ≤ (c1 + ck) * H ^ (n - 1) := by
          exact Nat.mul_le_mul_right _ hle
    · have hk2 : 2 ≤ k := by omega
      have hb := hasSmallFactor_large_pointwise n H hn3 hH hk2 (by omega : k ≤ n / 2)
      have hle : ck ≤ c1 + ck := Nat.le_add_left ck c1
      calc
        (HasSmallFactor n H k).ncard ≤ ck * H ^ (n - 1) := by simpa [ck] using hb
        _ ≤ (c1 + ck) * H ^ (n - 1) := by
          exact Nat.mul_le_mul_right _ hle
  calc
    (RedBox n H).ncard ≤ ∑ k ∈ Finset.Icc 1 (n / 2), (HasSmallFactor n H k).ncard := hsum
    _ ≤ ∑ k ∈ Finset.Icc 1 (n / 2), (c1 + ck) * H ^ (n - 1) := Finset.sum_le_sum hterm
    _ = (Finset.Icc 1 (n / 2)).card * ((c1 + ck) * H ^ (n - 1)) := by
      rw [Finset.sum_const]
      simp
    _ = (n / 2) * (c1 + ck) * H ^ (n - 1) := by
      rw [show (Finset.Icc 1 (n / 2)).card = n / 2 by simp]
      ring
    _ = RedBoxConst n * H ^ (n - 1) := by
      rw [RedBoxConst]

/-- **Theorem (van der Waerden / Chela): the reducible polynomials in the box
are `O(H^(n-1))` for `n ≥ 3`.** -/
theorem redBox_isBigO (n : ℕ) (hn : 3 ≤ n) :
    (fun H : ℕ => ((RedBox n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  refine IsBigO.of_bound (RedBoxConst n : ℝ) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with H hH
  have hb := redBox_card_pointwise n H hn hH
  have hf0 : (0 : ℝ) ≤ ((RedBox n H).ncard : ℝ) := by exact_mod_cast Nat.zero_le _
  have hg0 : (0 : ℝ) ≤ ((H : ℕ) ^ (n - 1) : ℝ) := by positivity
  rw [Real.norm_of_nonneg hf0, Real.norm_of_nonneg hg0]
  exact_mod_cast hb

end MainTheorem


/-- Reducible box polynomials are among the bad ones counted by `E n H`. -/
theorem redBox_subset_Bad (n H : ℕ) : RedBox n H ⊆ Bad n H := by
  intro p hp
  rcases hp with ⟨hbox, hred⟩
  exact reducible_mem_Bad n H p hbox hred



section IrreducibleSplit

/-- The irreducible bad polynomials (i.e. bad and not reducible).  For a
monic polynomial "not reducible (over ℤ with monic factors)" coincides with
irreducibility over ℚ (Gauss), so this is the genuinely irreducible part of
the van der Waerden problem. -/
def IrreducibleBad (n H : ℕ) : Set ℤ[X] :=
  {p | p ∈ Bad n H ∧ ¬ Reducible p}

/-- Irreducible bad polynomials are bad (trivial), and their reducible
companions are exactly `RedBox`. -/
theorem irreducibleBad_subset_Bad (n H : ℕ) : IrreducibleBad n H ⊆ Bad n H := by
  intro p hp
  exact hp.1

/-- Every bad polynomial is either reducible (in the `RedBox`) or
irreducible (in the `IrreducibleBad`).  This is the exact decomposition
that splits `E n H` into the reducible part (already `O(H^(n-1))` via
`redBox_isBigO`) and the irreducible part that the Cases I–III of the paper
bound. -/
theorem bad_subset_redBox_union_irrBad (n H : ℕ) :
    Bad n H ⊆ RedBox n H ∪ IrreducibleBad n H := by
  intro p hp
  by_cases hred : Reducible p
  · left
    exact ⟨Bad_subset_Box n H hp, hred⟩
  · right
    exact ⟨hp, hred⟩

/-- `E n H ≤ #RedBox + #IrreducibleBad` — the counting-level version of the
splitting that the endgame uses (`IsBigO.add` on the two bounds). -/
theorem E_le_redBox_add_irrBad (n H : ℕ) :
    E n H ≤ (RedBox n H).ncard + (IrreducibleBad n H).ncard := by
  rw [E_eq_ncard_bad]
  have hBox : (Box n H).Finite := box_finite n H
  have hRed : (RedBox n H).Finite := hBox.subset (by
    intro p hp; exact hp.1)
  have hIrr : (IrreducibleBad n H).Finite := hBox.subset (by
    intro p hp
    exact Bad_subset_Box n H hp.1)
  calc
    (Bad n H).ncard ≤ (RedBox n H ∪ IrreducibleBad n H).ncard :=
      Set.ncard_le_ncard (bad_subset_redBox_union_irrBad n H)
        (Set.Finite.union hRed hIrr)
    _ ≤ (RedBox n H).ncard + (IrreducibleBad n H).ncard :=
      Set.ncard_union_le _ _

end IrreducibleSplit



/-- **Endgame glue.**  Once the irreducible part is bounded
(`#IrreducibleBad n H = O(H^(n-1))`), the reducible part (`redBox_isBigO`)
gives the theorem: `E n H = O(H^(n-1))`.  This lemma is what replaces the
`sorry` in `Submission.lean` (with `E_eq_ncard_bad`). -/




theorem E_isBigO_of_irrBad (n : ℕ) (hn : 3 ≤ n)
    (hIrr : (fun H : ℕ => ((IrreducibleBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  have hRed : (fun H : ℕ => ((RedBox n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := redBox_isBigO n hn
  have hE_le : ∀ᶠ H : ℕ in atTop, E n H ≤ (RedBox n H).ncard + (IrreducibleBad n H).ncard := by
    filter_upwards with H
    exact E_le_redBox_add_irrBad n H
  have hE : (fun H : ℕ => (E n H : ℝ)) =O[atTop]
      (fun H : ℕ => (((RedBox n H).ncard + (IrreducibleBad n H).ncard : ℕ) : ℝ)) := by
    exact Commons.Analysis.Asymptotics.isBigO_of_eventually_le
      (fun H : ℕ => E n H)
      (fun H : ℕ => (RedBox n H).ncard + (IrreducibleBad n H).ncard)
      hE_le
  have hSum : (fun H : ℕ => (((RedBox n H).ncard + (IrreducibleBad n H).ncard : ℕ) : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
    simpa [Nat.cast_add] using hRed.add hIrr
  exact hE.trans hSum


section IrreducibilityGauss

/-- A monic polynomial of positive degree is not a unit. -/
lemma monic_natDegree_pos_not_isUnit {p : ℤ[X]} (hpmon : p.Monic) (hpdeg : 1 ≤ p.natDegree) :
    ¬ IsUnit p := by
  rintro hu
  have hdeg : p.natDegree = 0 := by
    rcases (Polynomial.isUnit_iff.mp hu) with ⟨r, hru, hCr⟩
    rw [← hCr]
    exact Polynomial.natDegree_C r
  omega

/-- A monic polynomial of positive degree which is a product of two non-units
over `ℤ` admits a `Reducible` (monic, positive degree) factorisation: the
leading coefficients multiply to `1` in `ℤ`, hence are `±1`, so the factors
are monic up to sign. -/
lemma monicFactor_of_mul_eq_monic {p a b : ℤ[X]} (hpmon : p.Monic)
    (_hpdeg : 1 ≤ p.natDegree) (hprod : a * b = p) (ha : ¬ IsUnit a) (hb : ¬ IsUnit b) :
    ∃ g h : ℤ[X], g.Monic ∧ h.Monic ∧ 1 ≤ g.natDegree ∧ 1 ≤ h.natDegree ∧ g * h = p := by
  classical
  have hpa0 : p ≠ 0 := hpmon.ne_zero
  have ha0 : a ≠ 0 := by
    intro h
    apply hpa0
    rw [← hprod, h, zero_mul]
  have hb0 : b ≠ 0 := by
    intro h
    apply hpa0
    rw [← hprod, h, mul_zero]
  have hlc : a.leadingCoeff * b.leadingCoeff = 1 := by
    calc
      a.leadingCoeff * b.leadingCoeff = (a * b).leadingCoeff := by rw [Polynomial.leadingCoeff_mul]
      _ = p.leadingCoeff := by rw [hprod]
      _ = 1 := hpmon.leadingCoeff
  have hua : IsUnit a.leadingCoeff := by
    rw [isUnit_iff_exists_inv]
    exact ⟨b.leadingCoeff, hlc⟩
  rcases (Int.isUnit_iff.mp hua) with hlca | hlca
  · -- lc a = 1 : both a and b are monic
    have ham : a.Monic := by
      change a.leadingCoeff = 1
      exact hlca
    have hblc : b.leadingCoeff = 1 := by
      change a.leadingCoeff * b.leadingCoeff = 1 at hlc
      simpa [hlca] using hlc
    have hbm : b.Monic := by
      change b.leadingCoeff = 1
      exact hblc
    have hda : 1 ≤ a.natDegree := by
      by_contra h
      have hd0 : a.natDegree = 0 := by omega
      have haC : a = C (a.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd0
      have hc0 : a.coeff 0 = 1 := by
        calc
          a.coeff 0 = a.leadingCoeff := by
            rw [← hd0]
            exact Polynomial.coeff_natDegree
          _ = 1 := by simpa using ham.leadingCoeff
      have ha1 : a = 1 := by
        rw [haC, hc0]
        simp
      exact ha (by rw [ha1]; simp)
    have hdb : 1 ≤ b.natDegree := by
      by_contra h
      have hd0 : b.natDegree = 0 := by omega
      have hbC : b = C (b.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd0
      have hc0 : b.coeff 0 = 1 := by
        calc
          b.coeff 0 = b.leadingCoeff := by
            rw [← hd0]
            exact Polynomial.coeff_natDegree
          _ = 1 := by simpa using hbm.leadingCoeff
      have hb1 : b = 1 := by
        rw [hbC, hc0]
        simp
      exact hb (by rw [hb1]; simp)
    exact ⟨a, b, ham, hbm, hda, hdb, hprod⟩
  · -- lc a = -1 : -a and -b are monic
    have hblc : b.leadingCoeff = -1 := by
      change a.leadingCoeff * b.leadingCoeff = 1 at hlc
      have h : (-1 : ℤ) * b.leadingCoeff = 1 := by simpa [hlca] using hlc
      omega
    have hgam : (-a).Monic := by
      change (-a).leadingCoeff = 1
      simp [hlca]
    have hgbm : (-b).Monic := by
      change (-b).leadingCoeff = 1
      simp [hblc]
    have hda : 1 ≤ a.natDegree := by
      by_contra h
      have hd0 : a.natDegree = 0 := by omega
      have haC : a = C (a.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd0
      have hc0 : a.coeff 0 = -1 := by
        calc
          a.coeff 0 = a.leadingCoeff := by
            rw [← hd0]
            exact Polynomial.coeff_natDegree
          _ = -1 := hlca
      have ha1 : a = -1 := by
        rw [haC, hc0]
        simp
      have ha1' : IsUnit a := by
        rw [ha1]
        simp
      exact ha ha1'
    have hdb : 1 ≤ b.natDegree := by
      by_contra h
      have hd0 : b.natDegree = 0 := by omega
      have hbC : b = C (b.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd0
      have hc0 : b.coeff 0 = -1 := by
        calc
          b.coeff 0 = b.leadingCoeff := by
            rw [← hd0]
            exact Polynomial.coeff_natDegree
          _ = -1 := hblc
      have hb1 : b = -1 := by
        rw [hbC, hc0]
        simp
      have hb1' : IsUnit b := by
        rw [hb1]
        simp
      exact hb hb1'
    refine ⟨-a, -b, hgam, hgbm, ?_, ?_, ?_⟩
    · simpa using hda
    · simpa using hdb
    · simpa using hprod

/-- For a **monic** integer polynomial of positive degree, "not `Reducible`"
(the monic-factor notion of `Submission.Vdw.Reducible`) is exactly
irreducibility over `ℤ`. -/
theorem irreducible_int_iff_not_reducible {p : ℤ[X]} (hpmon : p.Monic) (hpdeg : 1 ≤ p.natDegree) :
    Irreducible p ↔ ¬ Reducible p := by
  constructor
  · intro hpirr hred
    rcases hred with ⟨g, h, hgm, hhm, hgd, hhd, hprod⟩
    have hgnot : ¬ IsUnit g := monic_natDegree_pos_not_isUnit hgm hgd
    have hhnot : ¬ IsUnit h := monic_natDegree_pos_not_isUnit hhm hhd
    have hq : ∀ a b : ℤ[X], p = a * b → IsUnit a ∨ IsUnit b := by
      simpa using (irreducible_iff.mp hpirr).2
    rcases hq g h (by rw [hprod]) with hgu | hhu
    · exact hgnot hgu
    · exact hhnot hhu
  · intro hnot
    rw [irreducible_iff]
    constructor
    · exact monic_natDegree_pos_not_isUnit hpmon hpdeg
    · intro a b hprod
      by_contra h
      have hconj : ¬ IsUnit a ∧ ¬ IsUnit b := by
        exact not_or.mp h
      have hred := monicFactor_of_mul_eq_monic hpmon hpdeg (p := p) (a := a) (b := b) hprod.symm
        hconj.1 hconj.2
      exact hnot hred

/-- **Gauss for the irreducible part:** a monic integer polynomial of
positive degree which is not `Reducible` is irreducible over `ℚ`
(`Monic.irreducible_iff_irreducible_map_fraction_map`). -/
theorem not_reducible_irreducible_rat {p : ℤ[X]} (hpmon : p.Monic) (hpdeg : 1 ≤ p.natDegree)
    (hnot : ¬ Reducible p) : Irreducible (p.map (algebraMap ℤ ℚ)) := by
  have hirrZ : Irreducible p := (irreducible_int_iff_not_reducible hpmon hpdeg).2 hnot
  exact (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map hpmon).1 hirrZ

/-- Members of `IrreducibleBad` are irreducible over `ℚ` — the genuine
irreducibility of the irreducible half, under which the Galois-group analysis
(transitivity of the natural action, Jordan, imprimitive/primitive dichotomy)
applies to `IrreducibleBad`. -/
theorem irreducibleBad_mem_irreducible_rat {n H : ℕ} {p : ℤ[X]} (hn : 1 ≤ n)
    (hp : p ∈ IrreducibleBad n H) : Irreducible (p.map (algebraMap ℤ ℚ)) := by
  rcases hp with ⟨hbad, hnotred⟩
  rcases hbad with ⟨hpmon, hpdeg, _⟩
  have hdeg : p.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some hpdeg
  exact not_reducible_irreducible_rat hpmon (by omega : 1 ≤ p.natDegree) hnotred

/-- Conversely, an irreducible (over `ℚ`) box polynomial is not `Reducible`. -/
theorem irreducible_rat_not_reducible {n H : ℕ} {p : ℤ[X]} (hn : 1 ≤ n) (hp : p ∈ Box n H)
    (hirr : Irreducible (p.map (algebraMap ℤ ℚ))) : ¬ Reducible p := by
  rcases hp with ⟨hpmon, hpdeg, _⟩
  have hdeg : p.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some hpdeg
  have hmon : p.Monic := hpmon
  have hirrZ : Irreducible p :=
    (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map hmon).2 hirr
  exact (irreducible_int_iff_not_reducible hmon (by omega : 1 ≤ p.natDegree)).1 hirrZ

/-- A box polynomial is irreducible over `ℚ` iff it is not `Reducible`. -/
theorem box_polynomial_irreducible_rat_iff_not_reducible {n H : ℕ} {p : ℤ[X]}
    (hp : p ∈ Box n H) (hn : 1 ≤ n) :
    Irreducible (p.map (algebraMap ℤ ℚ)) ↔ ¬ Reducible p := by
  constructor
  · exact irreducible_rat_not_reducible hn hp
  · intro hnot
    rcases hp with ⟨hpmon, hpdeg, _⟩
    have hdeg : p.natDegree = n := Polynomial.natDegree_eq_of_degree_eq_some hpdeg
    exact not_reducible_irreducible_rat hpmon (by omega : 1 ≤ p.natDegree) hnot

end IrreducibilityGauss
end Submission.Vdw
