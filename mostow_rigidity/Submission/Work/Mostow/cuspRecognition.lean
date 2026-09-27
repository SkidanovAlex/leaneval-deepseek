import Mathlib
import Submission.Work.Mostow.cuspDefs
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.deepCusp
import Submission.Work.Mostow.properAction
import Submission.Work.Mostow.boundedOrbitFixed
import Submission.Work.Mostow.cruxFixedPoint
import Submission.Work.Mostow.commutingPairDependent
import Submission.Work.Mostow.Margulis.bdFix_size_of_no_fixed_point
import Submission.Work.Mostow.pairStabDefs
import Submission.Work.Mostow.pairStabCocycleDiscrete
import Submission.Work.Mostow.cuspTwoFixed
import Submission.Work.Mostow.cuspLoxContra
import Submission.Work.Mostow.cuspParabolicHasZ2

/-!
# Area C2 — `cuspRecognition : CuspRecognitionProp n`   (Prasad)

An abstract isomorphism `f : Γ ≃* Λ` of lattices in `PO(n,1)` maps parabolic elements to parabolic
elements (`n ≥ 3` is essential: cusped lattices in `ℍ²` are free).

Route (the group-theoretic property `HasZ2` of `cuspDefs`: a free abelian rank-two subgroup inside
the centraliser of a power of `γ`):

* `cusp_parabolic_hasZ2` : in a lattice, a parabolic element has `HasZ2`.  Geometrically: the cusp
  stabiliser of its fixed point `ξ` preserves all horospheres at `ξ` (that the level does not shift
  is exactly `hG`'s horoball-invariance clause), acts properly discontinuously (discreteness of
  `Γ`) and cocompactly (`hG`) on the horosphere, which is a Euclidean `E^{n-1}` (`horSpec`); by
  Bieberbach (`hBb`, `cuspZ2`) it contains a finite-index translation subgroup of rank `n-1 ≥ 2`,
  which is abelian.
* `HasZ2.map` : `HasZ2` is invariant under abstract isomorphism.
* `cusp_hasZ2_parabolic` : in a lattice, an infinite-order element with `HasZ2` is parabolic.  If
  `γ` has no interior fixed point and positive translation length, `cruxFixedPoint` gives a fixed
  boundary point `ξ`; if the Busemann cocycle at `ξ` vanishes then `deepCusp` contradicts the
  positive translation length, otherwise `ematFix`/`bdFixIff`/`eigNull`/`eigRecip` produce a second
  fixed boundary point `η` with non-vanishing cocycle; `pairStab` then says `Fix_Sph(γ) = {ξ, η}`,
  so commuting elements permute the pair, hence their squares fix `ξ` and `η`, and the discreteness
  of the lattice (`pairStabCocycleDiscrete`) together with the pure group theory
  (`commutingPairDependent`) forces a relation `a^i b^j = 1`, contradicting `HasZ2`.
-/

namespace Work.Mostow

open LeanEval.Geometry.MostowRigidity Submission.Mostow MeasureTheory

noncomputable section

variable {n : ℕ}

/-! ## The Busemann ray -/

lemma cusp_busemann_ray (hI : HypIsometryProp n) (ξ : E n) (hξ : ξ ∈ Sph n) (t : ℝ) :
    busemann ξ (Real.sinh t • ξ) = -t := by
  have hnorm : ‖ξ‖ = 1 := by
    simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
  have h1 : tpart (Real.sinh t • ξ) = Real.cosh t := by
    have hsq : ‖Real.sinh t • ξ‖ ^ 2 = Real.sinh t ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hnorm, one_pow, mul_one]
    rw [tpart, hsq]
    have h2 : 1 + Real.sinh t ^ 2 = Real.cosh t ^ 2 := by
      rw [Real.cosh_sq]; ring
    rw [h2, Real.sqrt_sq (le_of_lt (Real.cosh_pos t))]
  have h2 : inner ℝ (Real.sinh t • ξ) ξ = Real.sinh t := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hnorm]
    ring
  rw [busemann, h1, h2, Real.cosh_sub_sinh, Real.log_exp]

lemma cusp_busemann_surjective (hI : HypIsometryProp n) (ξ : E n) (hξ : ξ ∈ Sph n) (y : ℝ) :
    ∃ u : E n, busemann ξ u = y :=
  ⟨Real.sinh (-y) • ξ, by rw [cusp_busemann_ray hI ξ hξ]; ring⟩

/-- If `g` fixes `ξ` (so that the Busemann cocycle `c` with `busemann ξ (g•u) = busemann ξ u + c`
exists) and preserves the horoball of level `t` at `ξ`, then `c = 0`. -/
lemma cusp_cocycle_eq_zero_of_horoball (hI : HypIsometryProp n)
    (g : PO n 1) (ξ : E n) (hξ : ξ ∈ Sph n) (t c : ℝ)
    (hhor : ∀ u : E n, g • u ∈ horoball ξ t ↔ u ∈ horoball ξ t)
    (hc : ∀ u : E n, busemann ξ (g • u) = busemann ξ u + c) :
    c = 0 := by
  obtain ⟨u, hu⟩ := cusp_busemann_surjective hI ξ hξ (t - c / 2)
  have h1 := hhor u
  simp only [horoball, Set.mem_ofPred_eq] at h1
  rw [hc u, hu] at h1
  have hA' : (t - c / 2 + c < t) ↔ (c < 0) := by constructor <;> intro h' <;> linarith
  have hB' : (t - c / 2 < t) ↔ (0 < c) := by constructor <;> intro h' <;> linarith
  have h2 : (c < 0) ↔ (0 < c) := by rw [← hA', ← hB']; exact h1
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have : 0 < c := h2.mp h
    linarith
  · have : c < 0 := h2.mpr h
    linarith


/-! ## The Busemann cocycle is additive on a point stabiliser -/

lemma cusp_beta_add (hA : POActionProp n) (hI : HypIsometryProp n) (ξ : E n) (hξ : ξ ∈ Sph n)
    (g h : PO n 1) (hg : bd g ξ = ξ) (hh : bd h ξ = ξ) :
    busemann ξ ((g * h) • (0 : E n)) =
      busemann ξ (g • (0 : E n)) + busemann ξ (h • (0 : E n)) := by
  have hB : POBasic n := POBasic.ofProp hA
  have hJ : HypIsoData n := HypIsoData.ofProp hI
  have h1 : (g * h) • (0 : E n) = g • (h • (0 : E n)) := hB.mul_smul g h 0
  rw [h1]
  have h2 := hJ.busemann_cocycle g ξ (h • (0 : E n)) hξ
  rw [hg] at h2
  rw [h2]
  ring

/-! ## Parabolic elements have infinite order -/

/-- A parabolic element has infinite order: a finite-order element has a bounded orbit, hence a
fixed point (`boundedOrbitFixed`), contradicting `IsParabolic`'s first clause. -/
lemma cusp_parabolic_infinite (n : ℕ) (hn : 1 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (g : PO n 1) (hpar : IsParabolic g) (m : ℕ) (hm : 0 < m) : g ^ m ≠ 1 := by
  intro hpow
  have hbdd : ∃ R : ℝ, ∀ k : ℕ, hdist (0 : E n) ((g ^ k) • (0 : E n)) ≤ R := by
    refine ⟨∑ r ∈ Finset.range m, hdist (0 : E n) ((g ^ r) • (0 : E n)), fun k => ?_⟩
    rw [pow_eq_pow_mod k hpow]
    exact Finset.single_le_sum (fun i _ => hdist_nonneg (0 : E n) ((g ^ i) • (0 : E n)))
      (Finset.mem_range.mpr (Nat.mod_lt k hm))
  obtain ⟨u, hu⟩ := boundedOrbitFixed n hn hA hI g (0 : E n) hbdd
  exact hpar.1 u hu


/-- A fixed-point-free isometry with two distinct fixed boundary points has no third one
(`bdFix_not_three`, Margulis area). -/
lemma cusp_no_three (n : ℕ) (hn : 1 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (g : PO n 1) (hne : ∀ u : E n, g • u ≠ u) {ξ η : E n} (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n)
    (hξη : ξ ≠ η) (hξf : bd g ξ = ξ) (hηf : bd g η = η) :
    ∀ ζ : E n, ζ ∈ Sph n → bd g ζ = ζ → ζ = ξ ∨ ζ = η := by
  intro ζ hζ hζf
  by_contra hcon
  push_neg at hcon
  exact Work.Mostow.Margulis.bdFix_not_three n hn hA hI g hne ξ η ζ hξ hη hζ hξη hcon.1.symm hcon.2.symm hξf hηf hζf


/-! ## Powers in a point stabiliser -/

/-- Powers of an element fixing a boundary point fix it too. -/
lemma cusp_bd_pow_fix (hA : POActionProp n) (g : PO n 1) {ξ : E n} (hξ : ξ ∈ Sph n)
    (hfix : bd g ξ = ξ) (m : ℕ) : bd (g ^ m) ξ = ξ := by
  have hP : POBasic n := POBasic.ofProp hA
  induction m with
  | zero => simpa using hP.bd_one ξ hξ
  | succ m ih => rw [pow_succ, hP.bd_mul (g ^ m) g ξ hξ, hfix]; exact ih

/-- The Busemann cocycle of a point stabiliser is additive along powers. -/
lemma cusp_busemann_pow (hA : POActionProp n) (hI : HypIsometryProp n) (g : PO n 1) {ξ : E n}
    (hξ : ξ ∈ Sph n) (hfix : bd g ξ = ξ) (m : ℕ) :
    busemann ξ ((g ^ m) • (0 : E n)) = (m : ℝ) * busemann ξ (g • (0 : E n)) := by
  have hP : POBasic n := POBasic.ofProp hA
  have hJ : HypIsoData n := HypIsoData.ofProp hI
  induction m with
  | zero => simp [hP.one_smul, busemann_zero]
  | succ m ih =>
    have hc := hJ.busemann_cocycle g ξ ((g ^ m) • (0 : E n)) hξ
    rw [hfix] at hc
    rw [pow_succ', hP.mul_smul, hc, ih]
    push_cast
    ring

/-- **The point of the geodesic with endpoints `ξ ≠ η`.**  Every isometry `g` fixing both boundary
points `ξ` and `η` translates the point `pairPoint ξ η` by exactly `|busemann ξ (g • 0)|`. -/
lemma cusp_lox_pair (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (ξ η : E n) (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n) (hne : ξ ≠ η) :
    ∃ p : E n, ∀ g : PO n 1, bd g ξ = ξ → bd g η = η →
      hdist p (g • p) = |busemann ξ (g • (0 : E n))| :=
  ⟨pairPoint ξ η, fun g hgξ hgη => by
    obtain ⟨lam, _hlamne, hlam⟩ := emat_eigen_of_bd g hξ hgξ
    obtain ⟨μ, _hμne, hμ⟩ := emat_eigen_of_bd g hη hgη
    have hlamμ : lam * μ = 1 := eigen_mul_eq_one g hξ hη hne hlam hμ
    obtain ⟨_hlev, hlampos, hbus⟩ := lev_emat_eigen g hξ hlam
    rw [hdist_pairPoint g ξ η hξ hη hne hlam hμ hlamμ hlampos, hbus, abs_neg]⟩

/-- **A third fixed boundary point kills the cocycle.**  If `g` fixes `ξ ≠ η` and also a third
boundary point `ζ`, then its Busemann cocycle at `ξ` vanishes. -/
lemma cusp_lox_third (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (ξ η : E n) (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n) (hne : ξ ≠ η) :
    ∀ g : PO n 1, bd g ξ = ξ → bd g η = η →
      ∀ ζ ∈ Sph n, ζ ≠ ξ → ζ ≠ η → bd g ζ = ζ → busemann ξ (g • (0 : E n)) = 0 := by
  intro g hgξ hgη ζ hζ hζξ hζη hgζ
  obtain ⟨lam, _hlamne, hlam⟩ := emat_eigen_of_bd g hξ hgξ
  obtain ⟨μ, _hμne, hμ⟩ := emat_eigen_of_bd g hη hgη
  have hlamμ : lam * μ = 1 := eigen_mul_eq_one g hξ hη hne hlam hμ
  obtain ⟨ρ, _hρne, hρ⟩ := emat_eigen_of_bd g hζ hgζ
  obtain ⟨_hlev, hlampos, hbus⟩ := lev_emat_eigen g hξ hlam
  have hlamμeq : lam = μ := eigen_eq_of_third g hξ hη hζ hζξ hζη hlam hμ hρ
  have hsq : lam ^ 2 = 1 := by
    have h : lam * lam = 1 := by
      rw [← hlamμeq] at hlamμ
      exact hlamμ
    rwa [pow_two]
  have hlam1 : lam = 1 := by
    rcases sq_eq_one_iff.1 hsq with h | h
    · exact h
    · rw [h] at hlampos; norm_num at hlampos
  rw [hbus, hlam1, Real.log_one, neg_zero]

/-! ## The two halves of the argument -/

/-- **Half A** (chapter `cuspParabolicHasZ2`): in a lattice, a parabolic element has `HasZ2`. -/
lemma cusp_parabolic_hasZ2 (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hBb : ∀ m, BieberbachProp m) (hG : GeomFiniteProp n) (Γ : Subgroup (PO n 1))
    (hΓ : HypLattice Γ) (γ : Γ) (hpar : IsParabolic (γ : PO n 1)) : HasZ2 γ :=
  cuspParabolicHasZ2 n hn hA hI hBb hG Γ hΓ γ hpar

/-- **Half B.**  In a lattice `Λ`, an infinite-order element with `HasZ2` is parabolic. -/
lemma cusp_hasZ2_parabolic (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hG : GeomFiniteProp n) (Λ : Subgroup (PO n 1)) (hΛ : HypLattice Λ) (γ : Λ)
    (hinf : ∀ m : ℕ, 0 < m → γ ^ m ≠ 1) (hz : HasZ2 γ) : IsParabolic (γ : PO n 1) := by
  obtain ⟨k, hk, a, b, ha, hb, hab, hind⟩ := hz
  by_contra hnot
  have hsplit : (∃ u : E n, (γ : PO n 1) • u = u) ∨
      (∃ δ : ℝ, 0 < δ ∧ ∀ u : E n, δ ≤ hdist u ((γ : PO n 1) • u)) := by
    by_cases hell : ∃ u : E n, (γ : PO n 1) • u = u
    · exact Or.inl hell
    · refine Or.inr ?_
      push_neg at hell
      by_contra hcon
      push_neg at hcon
      exact hnot ⟨hell, hcon⟩
  rcases hsplit with ⟨u, hu⟩ | ⟨δ, hδ0, hδ⟩
  · -- elliptic case: finite point stabilisers make `γ` of finite order
    have hB : POBasic n := POBasic.ofProp hA
    have hfin : {γ' : Λ | (γ' : PO n 1) • u = u}.Finite := by
      have hK : IsCompact ({u} : Set (E n)) := isCompact_singleton
      have h := properAction n hn hA hI Λ hΛ.1 u ({u} : Set (E n)) hK
      simpa using h
    have hmem : ∀ i : ℕ, γ ^ i ∈ {γ' : Λ | (γ' : PO n 1) • u = u} := by
      intro i
      show ((γ ^ i : Λ) : PO n 1) • u = u
      induction i with
      | zero => simp [hB.one_smul]
      | succ i ih =>
        rw [pow_succ, Subgroup.coe_mul, hB.mul_smul, hu, ih]
    -- pigeonhole: the powers `γ ^ i` all lie in the finite stabiliser
    obtain ⟨i, hi, j, hj, hij, hpowij⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to
        (s := Finset.range (hfin.toFinset.card + 1)) (t := hfin.toFinset)
        (by rw [Finset.card_range]; omega)
        (f := fun i : ℕ => γ ^ i)
        (fun x _ => (Set.Finite.mem_toFinset hfin).mpr (hmem x))
    exfalso
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · refine hinf (j - i) (by omega) ?_
      have h1 : γ ^ j = γ ^ i * γ ^ (j - i) := by
        rw [← pow_add, Nat.add_sub_of_le hlt.le]
      have h2 : γ ^ i * γ ^ (j - i) = γ ^ i * 1 := by rw [← h1, ← hpowij, mul_one]
      exact mul_left_cancel h2
    · refine hinf (i - j) (by omega) ?_
      have h1 : γ ^ i = γ ^ j * γ ^ (i - j) := by
        rw [← pow_add, Nat.add_sub_of_le hlt.le]
      have h2 : γ ^ j * γ ^ (i - j) = γ ^ j * 1 := by rw [← h1, hpowij, mul_one]
      exact mul_left_cancel h2
  · -- loxodromic case: the classification argument (Z3-Z7 of the design)
    have hJ : HypIsoData n := HypIsoData.ofProp hI
    have hne : ∀ u : E n, (γ : PO n 1) • u ≠ u := by
      intro u hfix
      have h0 : hdist u ((γ : PO n 1) • u) = 0 := by
        rw [hfix]; exact (hJ.eq_zero u u).mpr rfl
      linarith [hδ u, hδ0]
    obtain ⟨ξ, η, hξ, hη, hξη, hξfix, hηfix, hβ0⟩ :=
      cuspTwoFixed n hn hA hI (γ : PO n 1) hne ⟨δ, hδ0, hδ⟩
    have hξfixk : bd (((γ : PO n 1)) ^ k) ξ = ξ := cusp_bd_pow_fix hA _ hξ hξfix k
    have hηfixk : bd (((γ : PO n 1)) ^ k) η = η := cusp_bd_pow_fix hA _ hη hηfix k
    have hβk : busemann ξ ((((γ : PO n 1)) ^ k) • (0 : E n)) ≠ 0 := by
      rw [cusp_busemann_pow hA hI (γ : PO n 1) hξ hξfix k]
      exact mul_ne_zero (by exact_mod_cast hk.ne') hβ0
    -- the point of the geodesic `(ξ,η)` and its two properties (`pairStab`'s content)
    have hpair := cusp_lox_pair n (by omega) hA hI ξ η hξ hη hξη
    have hthird := cusp_lox_third n (by omega) hA hI ξ η hξ hη hξη
    have hno3 : ∀ ζ : E n, ζ ∈ Sph n → bd (((γ : PO n 1)) ^ k) ζ = ζ → ζ = ξ ∨ ζ = η := by
      intro ζ hζ hζf
      by_contra hcon
      rw [not_or] at hcon
      exact hβk (hthird (((γ : PO n 1)) ^ k) hξfixk hηfixk ζ hζ hcon.1 hcon.2 hζf)
    obtain ⟨c, hdis, hker⟩ :=
      pairStabCocycleDiscrete n (by omega) hA hI Λ hΛ.1 ξ η hξ hη hξη hpair
    -- transport `hind` to `PO n 1`
    have hindPO : ∀ i j : ℤ, (a : PO n 1) ^ i * (b : PO n 1) ^ j = 1 → i = 0 ∧ j = 0 := by
      intro i j hij
      refine hind i j ?_
      exact Subtype.ext (by
        simpa only [Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_one] using hij)
    exact cuspLoxContra n hn hA hI Λ hΛ γ k hk a b ha hb hab hindPO ξ η hξ hη hξη
      hξfixk hηfixk hβk hno3 hpair ⟨c, hdis⟩ hker

/-! ## The main theorem -/

theorem cuspRecognition (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hBb : ∀ m, BieberbachProp m) (hG : GeomFiniteProp n) : CuspRecognitionProp n := by
  intro Γ Λ hΓ hΛ f γ hpar
  have hZ2 : HasZ2 γ := cusp_parabolic_hasZ2 n hn hA hI hBb hG Γ hΓ γ hpar
  have hZ2' : HasZ2 (f γ) := hZ2.map f
  have hinf : ∀ m : ℕ, 0 < m → (f γ) ^ m ≠ 1 := by
    intro m hm hpow
    have h1 : (γ ^ m : Γ) = 1 := f.injective (by rw [map_pow, hpow, map_one])
    have h2 : ((γ : PO n 1)) ^ m = 1 := by
      rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
    exact cusp_parabolic_infinite n (by omega) hA hI (γ : PO n 1) hpar m hm h2
  exact cusp_hasZ2_parabolic n hn hA hI hG Λ hΛ (f γ) hinf hZ2'

end

end Work.Mostow
