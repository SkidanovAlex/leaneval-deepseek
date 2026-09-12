import Mathlib
import Submission.GeometryOfNumbers.ExteriorCoordinates

/-!
# Diagonal linear maps of `ℝᵈ` and their exterior-power action (flow lattice, Part 1)

For `ℝᵈ = EuclideanSpace ℝ (Fin d)` with standard orthonormal basis `(B d)`, a coefficient
function `s : Fin d → ℝ` defines the diagonal linear map `scaleMap s` (pointwise
multiplication of coordinates).  Acting on the exterior power `⋀^k ℝᵈ` through
`exteriorPower.map`, such a map is diagonal in the standard exterior-power basis: the basis
vector at a `k`-subset `I` is an eigenvector with eigenvalue `∏_{i ∈ I} s i`
(`map_scaleMap_basis`).

With the two-scale coefficients `twoScale a b ℓ` (`a` on the first `ℓ` coordinates, `b` on
the rest) — e.g. `a = exp(-t/ℓ)`, `b = exp(t/(d-ℓ))`, the diagonal flow `a_t` of the paper —
the exterior-power action preserves the block decomposition `w = Σⱼ blockElem w j`
(components with `j` indices `≥ ℓ`): each block is an eigenspace with eigenvalue
`a^(k-j) * b^j` (`map_scaleMap_twoScale_blockElem`).  This is the linear-algebra input to
the "Dani correspondence" estimates (paper Prop 1) in the coordinate model.

All results here are Mathlib-only.
-/

noncomputable section

open BigOperators Module exteriorPower InnerProductGeometry
set_option autoImplicit false
set_option maxHeartbeats 1000000

open Submission.ExteriorCoordinates

namespace Submission.DiagonalFlow

@[ext] lemma rd_ext {d : ℕ} {x y : RD d} (h : ∀ i : Fin d, x i = y i) : x = y := by
  have hxy : x.ofLp = y.ofLp := funext (fun i => h i)
  calc
    x = WithLp.toLp (2 : ENNReal) (x.ofLp) := (WithLp.toLp_ofLp (p := (2 : ENNReal)) x).symm
    _ = WithLp.toLp (2 : ENNReal) (y.ofLp) := by rw [hxy]
    _ = y := WithLp.toLp_ofLp (p := (2 : ENNReal)) y

/-- Pointwise multiplication by `s` as a linear map of `ℝᵈ` (the "diagonal" linear maps). -/
def scaleMap {d : ℕ} (s : Fin d → ℝ) : RD d →ₗ[ℝ] RD d where
  toFun := fun x => (WithLp.toLp (2 : ENNReal) (fun i => s i * x i) : RD d)
  map_add' := by
    intro x y
    apply rd_ext
    intro i
    simp [mul_add]
  map_smul' := by
    intro c x
    apply rd_ext
    intro i
    simp
    ring

lemma scaleMap_apply {d : ℕ} (s : Fin d → ℝ) (x : RD d) (i : Fin d) :
    (scaleMap s x) i = s i * x i := by
  rfl

lemma scaleMap_basis {d : ℕ} (s : Fin d → ℝ) (i : Fin d) :
    scaleMap s ((B d) i) = s i • (B d) i := by
  apply rd_ext
  intro j
  rw [scaleMap_apply]
  simp [EuclideanSpace.basisFun_apply]
  by_cases hji : j = i
  · simp [hji]
  · simp [hji]

/-- Two-scale coefficient: `a` on the first `ℓ` coordinates, `b` on the rest. -/
def twoScale {d : ℕ} (a b : ℝ) (ℓ : ℕ) : Fin d → ℝ :=
  fun i => if i.val < ℓ then a else b

@[simp] lemma twoScale_apply {d : ℕ} (a b : ℝ) (ℓ : ℕ) (i : Fin d) :
    twoScale a b ℓ i = if i.val < ℓ then a else b := by
  rfl

/-- Extensionality for the exterior power of a family of vectors. -/
lemma ιMulti_smul_univ {d k : ℕ} (c : Fin k → ℝ) (v : Fin k → RD d) :
    exteriorPower.ιMulti ℝ k (fun r => c r • v r) =
      (Finset.univ.prod fun r : Fin k => c r) • exteriorPower.ιMulti ℝ k v := by
  exact AlternatingMap.map_smul_univ (exteriorPower.ιMulti ℝ k) c v

/-- The standard exterior-power basis vector at a subset is the wedge over the increasing
enumeration of the subset. (Kept local to keep the module dependency-light.) -/
lemma basisWedge_eq_enumWedge {d k : ℕ} (s : IDX d k) :
    (Bk d k) s = exteriorPower.ιMulti ℝ k (fun r : Fin k =>
      (B d) (Set.powersetCard.ofFinEmbEquiv.symm s r)) := by
  change (((B d).exteriorPower k).toBasis) s = exteriorPower.ιMulti ℝ k (fun r : Fin k =>
    (B d) (Set.powersetCard.ofFinEmbEquiv.symm s r))
  rw [OrthonormalBasis.toBasis_exteriorPower]
  rw [exteriorPower.basis_apply]
  rfl

/-- The enumeration `σ : Fin k ↪o Fin d` of a `k`-subset `I` has range exactly the finset `I`. -/
lemma enumWedge_range {d k : ℕ} (I : IDX d k) :
    Finset.univ.image (Set.powersetCard.ofFinEmbEquiv.symm I : Fin k → Fin d) =
      (I : Finset (Fin d)) := by
  classical
  let σ : Fin k → Fin d := Set.powersetCard.ofFinEmbEquiv.symm I
  have hset : (Set.range σ : Set (Fin d)) = ((I : Finset (Fin d)) : Set (Fin d)) := by
    ext j
    simpa using (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem (s := I) (i := j))
  -- two finsets with equal underlying sets are equal
  apply Finset.coe_injective
  simpa [Finset.coe_image] using hset

/-- Product over the subset equals the product over its increasing enumeration. -/
lemma prod_enumWedge {d k : ℕ} (s : Fin d → ℝ) (I : IDX d k) :
    (Finset.univ.prod fun r : Fin k => s (Set.powersetCard.ofFinEmbEquiv.symm I r)) =
      ((I : Finset (Fin d)).prod s) := by
  classical
  let σ : Fin k ↪o Fin d := Set.powersetCard.ofFinEmbEquiv.symm I
  have hσ : Set.InjOn (⇑σ) (↑(Finset.univ : Finset (Fin k))) := by
    intro a ha b hb hab
    exact (Set.powersetCard.ofFinEmbEquiv.symm I).injective hab
  calc
    (Finset.univ.prod fun r : Fin k => s (σ r)) =
        ((Finset.univ.image σ : Finset (Fin d)).prod s) := by
          rw [Finset.prod_image (s := (Finset.univ : Finset (Fin k))) (g := σ) hσ]
    _ = ((I : Finset (Fin d)).prod s) := by
          congr
          exact enumWedge_range (d := d) (k := k) I

/-- The action of a diagonal map on the standard exterior-power basis: the basis vector at
subset `I` is an eigenvector with eigenvalue `∏_{i ∈ I} s i`. -/
lemma map_scaleMap_basis {d k : ℕ} (s : Fin d → ℝ) (I : IDX d k) :
    exteriorPower.map k (scaleMap s) ((Bk d k) I : WK d k) =
      ((I : Finset (Fin d)).prod s) • ((Bk d k) I : WK d k) := by
  classical
  let σ : Fin k ↪o Fin d := Set.powersetCard.ofFinEmbEquiv.symm I
  have hb : ((Bk d k) I : WK d k) =
      exteriorPower.ιMulti ℝ k (fun r : Fin k => (B d) (σ r)) := by
    simpa [σ] using (basisWedge_eq_enumWedge (d := d) (k := k) I)
  calc
    exteriorPower.map k (scaleMap s) ((Bk d k) I : WK d k)
        = exteriorPower.map k (scaleMap s)
            (exteriorPower.ιMulti ℝ k (fun r : Fin k => (B d) (σ r))) := by rw [hb]
    _ = exteriorPower.ιMulti ℝ k (fun r : Fin k => s (σ r) • (B d) (σ r)) := by
          rw [exteriorPower.map_apply_ιMulti]
          apply congrArg (exteriorPower.ιMulti ℝ k)
          funext r
          exact scaleMap_basis s (σ r)
    _ = (Finset.univ.prod fun r : Fin k => s (σ r)) •
          exteriorPower.ιMulti ℝ k (fun r : Fin k => (B d) (σ r)) := by
          rw [ιMulti_smul_univ]
    _ = ((I : Finset (Fin d)).prod s) •
          exteriorPower.ιMulti ℝ k (fun r : Fin k => (B d) (σ r)) := by
          rw [prod_enumWedge (d := d) (k := k) (s := s) (I := I)]
    _ = ((I : Finset (Fin d)).prod s) • ((Bk d k) I : WK d k) := by rw [← hb]



/-- Product of the two-scale coefficients over a set of `k` indices of which exactly `j` lie
`≥ ℓ`: the value is `a^(k-j) * b^j`. -/
lemma twoScale_prod {d : ℕ} (a b : ℝ) (ℓ : ℕ) (I : Finset (Fin d)) (k j : ℕ)
    (hcard : I.card = k) (hge : (I.filter (fun i : Fin d => ℓ ≤ i.val)).card = j) :
    I.prod (twoScale a b ℓ) = a ^ (k - j) * b ^ j := by
  classical
  let P : Finset (Fin d) := I.filter (fun i : Fin d => i.val < ℓ)
  let Q : Finset (Fin d) := I.filter (fun i : Fin d => ℓ ≤ i.val)
  have hdisj : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro i hiP hiQ
    have h1p : i ∈ I ∧ i.val < ℓ := by simpa [P] using hiP
    have h1 : i.val < ℓ := h1p.2
    have h2p : i ∈ I ∧ ℓ ≤ i.val := by simpa [Q] using hiQ
    have h2 : ℓ ≤ i.val := h2p.2
    omega
  have hunion : P ∪ Q = I := by
    ext i
    by_cases hlt : i.val < ℓ
    · simp [P, Q, hlt]
    · have hgei : ℓ ≤ i.val := le_of_not_gt hlt
      simp [P, Q, hlt, hgei]
  calc
    I.prod (twoScale a b ℓ) = (P ∪ Q).prod (twoScale a b ℓ) := by rw [hunion]
    _ = P.prod (twoScale a b ℓ) * Q.prod (twoScale a b ℓ) := Finset.prod_union hdisj
    _ = a ^ P.card * b ^ Q.card := by
      congr 1
      · calc
          P.prod (twoScale a b ℓ) = P.prod (fun _ : Fin d => a) := by
            apply Finset.prod_congr rfl
            intro i hi
            have hltp : i ∈ I ∧ i.val < ℓ := by simpa [P] using hi
            simp [hltp.2]
          _ = a ^ P.card := by simp
      · calc
          Q.prod (twoScale a b ℓ) = Q.prod (fun _ : Fin d => b) := by
            apply Finset.prod_congr rfl
            intro i hi
            have hgeip : i ∈ I ∧ ℓ ≤ i.val := by simpa [Q] using hi
            simp [hgeip.2]
          _ = b ^ Q.card := by simp
    _ = a ^ (k - j) * b ^ j := by
      have hsum : P.card + Q.card = k := by
        rw [← Finset.card_union_of_disjoint hdisj]
        rw [hunion, hcard]
      have hQc : Q.card = j := by simpa [Q] using hge
      have hPc : P.card = k - j := by omega
      rw [hPc, hQc]

/-- The diagonal map with two-scale coefficients preserves each block of the exterior-power
decomposition, acting on block `j` as multiplication by `a^(k-j) * b^j`. -/
lemma map_scaleMap_twoScale_blockElem {d k ℓ j : ℕ} (a b : ℝ) (w : WK d k) :
    exteriorPower.map k (scaleMap (twoScale a b ℓ)) (blockElem (ℓ := ℓ) w j) =
      (a ^ (k - j) * b ^ j) • blockElem (ℓ := ℓ) w j := by
  classical
  let eig : ℝ := a ^ (k - j) * b ^ j
  let bl : Finset (IDX d k) := blockFinset (d := d) (k := k) (ℓ := ℓ) j
  unfold blockElem
  rw [map_sum]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [map_smul]
  rw [map_scaleMap_basis (d := d) (k := k) (s := twoScale a b ℓ) (I := s)]
  have hcard_s : ((s : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card = j := by
    simpa [blockFinset] using hs
  have hprod : ((s : Finset (Fin d)).prod (twoScale a b ℓ)) = eig := by
    simpa [eig] using (twoScale_prod (d := d) (a := a) (b := b) (ℓ := ℓ)
      (I := (s : Finset (Fin d))) (k := k) (j := j) (s.2) hcard_s)
  rw [hprod]
  -- wcoord w s • (eig • basis s) = eig • (wcoord w s • basis s)
  rw [smul_smul, smul_smul, mul_comm]


lemma basis_inner_dirac {d k : ℕ} (s t : IDX d k) :
    inner ℝ (((Bk d k) s : WK d k)) (((Bk d k) t : WK d k)) = if s = t then (1 : ℝ) else 0 := by
  classical
  by_cases h : s = t
  · subst t
    have h1 : ‖((Bk d k) s : WK d k)‖ = 1 := (Bk d k).orthonormal.norm_eq_one s
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℝ) (((Bk d k) s : WK d k))]
    simp [h1]
  · have hz : inner ℝ (((Bk d k) s : WK d k)) (((Bk d k) t : WK d k)) = 0 :=
      (Bk d k).orthonormal.inner_eq_zero h
    simp [h, hz]

lemma wcoord_smul_basis {d k : ℕ} (a : ℝ) (s t : IDX d k) :
    wcoord (d := d) (k := k) (a • ((Bk d k) s : WK d k)) t = if s = t then a else 0 := by
  classical
  rw [wcoord, OrthonormalBasis.repr_apply_apply]
  by_cases hst : s = t
  · subst t
    calc
      inner ℝ ((Bk d k) s : WK d k) (a • ((Bk d k) s : WK d k)) =
          a * inner ℝ ((Bk d k) s : WK d k) ((Bk d k) s : WK d k) := by
            exact inner_smul_right ((Bk d k) s : WK d k) ((Bk d k) s : WK d k) a
      _ = a := by
            rw [basis_inner_dirac s s]
            simp
      _ = if s = s then a else 0 := by
            simp
  · calc
      inner ℝ ((Bk d k) t : WK d k) (a • ((Bk d k) s : WK d k)) =
          a * inner ℝ ((Bk d k) t : WK d k) ((Bk d k) s : WK d k) := by
            exact inner_smul_right ((Bk d k) t : WK d k) ((Bk d k) s : WK d k) a
      _ = 0 := by
            rw [basis_inner_dirac t s]
            by_cases hts : t = s
            · exfalso
              exact hst hts.symm
            · simp [hts]
      _ = if s = t then a else 0 := by
            simp [hst]

lemma wcoord_blockElem {d k ℓ j : ℕ} (w : WK d k) (s : IDX d k) :
    wcoord (d := d) (k := k) (blockElem (d := d) (k := k) (ℓ := ℓ) w j) s =
      if s ∈ blockFinset (d := d) (k := k) (ℓ := ℓ) j then wcoord (d := d) (k := k) w s else 0 := by
  classical
  unfold blockElem
  rw [wcoord, OrthonormalBasis.repr_apply_apply]
  rw [inner_sum (blockFinset (d := d) (k := k) (ℓ := ℓ) j)
      (fun t => wcoord (d := d) (k := k) w t • ((Bk d k) t : WK d k))
      (((Bk d k) s : WK d k))]
  have hterm : ∀ t ∈ blockFinset (d := d) (k := k) (ℓ := ℓ) j,
      inner ℝ ((Bk d k) s : WK d k)
        (wcoord (d := d) (k := k) w t • ((Bk d k) t : WK d k)) =
        (if s = t then wcoord (d := d) (k := k) w t else 0) := by
    intro t ht
    calc
      inner ℝ ((Bk d k) s : WK d k)
          (wcoord (d := d) (k := k) w t • ((Bk d k) t : WK d k))
          = wcoord (d := d) (k := k) w t * inner ℝ ((Bk d k) s : WK d k) ((Bk d k) t : WK d k) := by
              exact inner_smul_right ((Bk d k) s : WK d k) ((Bk d k) t : WK d k) (wcoord (d := d) (k := k) w t)
      _ = wcoord (d := d) (k := k) w t * (if s = t then (1 : ℝ) else 0) := by
              rw [basis_inner_dirac s t]
      _ = if s = t then wcoord (d := d) (k := k) w t else 0 := by
              by_cases h : s = t <;> simp [h]
  rw [Finset.sum_congr rfl hterm]
  by_cases hs : s ∈ blockFinset (d := d) (k := k) (ℓ := ℓ) j
  · rw [if_pos hs]
    rw [Finset.sum_eq_single (s := blockFinset (d := d) (k := k) (ℓ := ℓ) j)
      (f := fun t : IDX d k => if s = t then wcoord (d := d) (k := k) w t else 0) s
      (by
        intro b hb hneq
        have hsb : s ≠ b := fun h => hneq h.symm
        simp [hsb])
      (by intro hnot; exact (hnot hs).elim)]
    simp
  · rw [if_neg hs]
    apply Finset.sum_eq_zero
    intro t ht
    have hts : s ≠ t := by
      intro hst
      exact hs (by simpa [hst] using ht)
    simp [hts]


/-- `wcoord` of zero is zero. -/
@[simp] lemma wcoord_zero {d k : ℕ} (s : IDX d k) :
    wcoord (d := d) (k := k) (0 : WK d k) s = 0 := by
  simp [wcoord]

/-- `wcoord` is ℝ-linear in the vector. -/
lemma wcoord_add {d k : ℕ} (x y : WK d k) (s : IDX d k) :
    wcoord (d := d) (k := k) (x + y) s = wcoord (d := d) (k := k) x s + wcoord (d := d) (k := k) y s := by
  simp [wcoord]

lemma wcoord_smul {d k : ℕ} (a : ℝ) (x : WK d k) (s : IDX d k) :
    wcoord (d := d) (k := k) (a • x) s = a * wcoord (d := d) (k := k) x s := by
  simp [wcoord]

/-- Extensionality of `k`-vectors through their Plücker coordinates. -/
lemma wk_ext {d k : ℕ} {x y : WK d k}
    (h : ∀ s : IDX d k, wcoord (d := d) (k := k) x s = wcoord (d := d) (k := k) y s) :
    x = y := by
  classical
  calc
    x = (Finset.univ : Finset (IDX d k)).sum (fun s =>
          wcoord (d := d) (k := k) x s • ((Bk d k) s : WK d k)) :=
        (sum_wcoord_smul_basis (d := d) (k := k) x).symm
    _ = (Finset.univ : Finset (IDX d k)).sum (fun s =>
          wcoord (d := d) (k := k) y s • ((Bk d k) s : WK d k)) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [h s]
    _ = y := sum_wcoord_smul_basis (d := d) (k := k) y

/-- `blockElem` is additive in the vector. -/
lemma blockElem_add {d k ℓ j : ℕ} (x y : WK d k) :
    blockElem (d := d) (k := k) (ℓ := ℓ) (x + y) j = blockElem (d := d) (k := k) (ℓ := ℓ) x j +
      blockElem (d := d) (k := k) (ℓ := ℓ) y j := by
  classical
  unfold blockElem
  calc
    (blockFinset (d := d) (k := k) (ℓ := ℓ) j).sum
        (fun t => wcoord (d := d) (k := k) (x + y) t • ((Bk d k) t : WK d k))
        = (blockFinset (d := d) (k := k) (ℓ := ℓ) j).sum
            (fun t => (wcoord (d := d) (k := k) x t + wcoord (d := d) (k := k) y t) • ((Bk d k) t : WK d k)) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [wcoord_add]
    _ = (blockFinset (d := d) (k := k) (ℓ := ℓ) j).sum
            (fun t => wcoord (d := d) (k := k) x t • ((Bk d k) t : WK d k) +
                      wcoord (d := d) (k := k) y t • ((Bk d k) t : WK d k)) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [add_smul]
    _ = (blockFinset (d := d) (k := k) (ℓ := ℓ) j).sum
            (fun t => wcoord (d := d) (k := k) x t • ((Bk d k) t : WK d k)) +
        (blockFinset (d := d) (k := k) (ℓ := ℓ) j).sum
            (fun t => wcoord (d := d) (k := k) y t • ((Bk d k) t : WK d k)) := by
            rw [Finset.sum_add_distrib]

/-- `blockElem` is ℝ-linear in the vector. -/
lemma blockElem_smul {d k ℓ j : ℕ} (a : ℝ) (x : WK d k) :
    blockElem (d := d) (k := k) (ℓ := ℓ) (a • x) j = a • blockElem (d := d) (k := k) (ℓ := ℓ) x j := by
  classical
  unfold blockElem
  calc
    (blockFinset (d := d) (k := k) (ℓ := ℓ) j).sum
        (fun t => wcoord (d := d) (k := k) (a • x) t • ((Bk d k) t : WK d k))
        = (blockFinset (d := d) (k := k) (ℓ := ℓ) j).sum
            (fun t => (a * wcoord (d := d) (k := k) x t) • ((Bk d k) t : WK d k)) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [wcoord_smul]
    _ = (blockFinset (d := d) (k := k) (ℓ := ℓ) j).sum
            (fun t => a • (wcoord (d := d) (k := k) x t • ((Bk d k) t : WK d k))) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [← smul_smul]
    _ = a • (blockFinset (d := d) (k := k) (ℓ := ℓ) j).sum
            (fun t => wcoord (d := d) (k := k) x t • ((Bk d k) t : WK d k)) := by
            rw [Finset.smul_sum]

/-- `blockElem` of zero is zero. -/
@[simp] lemma blockElem_zero {d k ℓ j : ℕ} :
    blockElem (d := d) (k := k) (ℓ := ℓ) (0 : WK d k) j = 0 := by
  simp [blockElem, wcoord]

/-- `blockElem` distributes over finset sums of scaled vectors (linearity). -/
lemma blockElem_sum {d k ℓ j : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℝ) (x : ι → WK d k) :
    blockElem (d := d) (k := k) (ℓ := ℓ) (s.sum (fun i => c i • x i)) j =
      s.sum (fun i => c i • blockElem (d := d) (k := k) (ℓ := ℓ) (x i) j) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s hnot ih =>
      simp [Finset.sum_insert hnot, blockElem_add, blockElem_smul, ih]


/-- Applying the block-`j` projection twice: on a vector already in block `j` it is
idempotent. -/
lemma blockElem_blockElem_idem {d k ℓ j : ℕ} (w : WK d k) :
    blockElem (d := d) (k := k) (ℓ := ℓ) (blockElem (d := d) (k := k) (ℓ := ℓ) w j) j =
      blockElem (d := d) (k := k) (ℓ := ℓ) w j := by
  classical
  apply wk_ext
  intro s
  rw [wcoord_blockElem (w := blockElem (d := d) (k := k) (ℓ := ℓ) w j) (s := s) (j := j)]
  rw [wcoord_blockElem (w := w) (s := s) (j := j)]
  by_cases hs : s ∈ blockFinset (d := d) (k := k) (ℓ := ℓ) j <;> simp [hs]

/-- Distinct blocks are orthogonal for the block projection: `blockElem (blockElem w i) j = 0`
for `i ≠ j`. -/
lemma blockElem_blockElem_of_ne {d k ℓ : ℕ} {i j : ℕ} (hij : i ≠ j) (w : WK d k) :
    blockElem (d := d) (k := k) (ℓ := ℓ) (blockElem (d := d) (k := k) (ℓ := ℓ) w i) j = 0 := by
  classical
  apply wk_ext
  intro s
  rw [wcoord_blockElem (w := blockElem (d := d) (k := k) (ℓ := ℓ) w i) (s := s) (j := j)]
  rw [wcoord_blockElem (w := w) (s := s) (j := i)]
  by_cases hs_j : s ∈ blockFinset (d := d) (k := k) (ℓ := ℓ) j
  · rw [if_pos hs_j]
    by_cases hs_i : s ∈ blockFinset (d := d) (k := k) (ℓ := ℓ) i
    · exfalso
      apply hij
      have hci : ((s : Finset (Fin d)).filter (fun a : Fin d => ℓ ≤ a.val)).card = i := by
        simpa [blockFinset] using hs_i
      have hcj : ((s : Finset (Fin d)).filter (fun a : Fin d => ℓ ≤ a.val)).card = j := by
        simpa [blockFinset] using hs_j
      omega
    · simp [hs_i]
  · simp [hs_j]


/-- The flow commutes with block projection: the `j`-th block of the flowed vector is the
eigenvalue `a^(k-j)*b^j` times the `j`-th block of the original vector.  (Together with
`map_scaleMap_twoScale_blockElem` this gives the whole block-eigenspace structure of the
diagonal flow on `⋀^k ℝᵈ`; `0 ≤ j ≤ k`.) -/
lemma blockElem_map_scaleMap_twoScale {d k ℓ j : ℕ} (a b : ℝ) (w : WK d k) (hj : j ≤ k) :
    blockElem (d := d) (k := k) (ℓ := ℓ)
        (exteriorPower.map k (scaleMap (twoScale a b ℓ)) w) j =
      (a ^ (k - j) * b ^ j) • blockElem (d := d) (k := k) (ℓ := ℓ) w j := by
  classical
  let f : WK d k →ₗ[ℝ] WK d k := exteriorPower.map k (scaleMap (twoScale a b ℓ))
  have hdec : (Finset.range (k + 1)).sum (fun i : ℕ =>
      blockElem (d := d) (k := k) (ℓ := ℓ) w i) = w :=
    sum_blockElem (d := d) (k := k) (ℓ := ℓ) w
  calc
    blockElem (d := d) (k := k) (ℓ := ℓ) (f w) j
        = blockElem (d := d) (k := k) (ℓ := ℓ) (f ((Finset.range (k + 1)).sum
            (fun i : ℕ => blockElem (d := d) (k := k) (ℓ := ℓ) w i))) j := by
            apply congrArg (fun z : WK d k => blockElem (d := d) (k := k) (ℓ := ℓ) z j)
            exact congrArg f hdec.symm
    _ = blockElem (d := d) (k := k) (ℓ := ℓ) ((Finset.range (k + 1)).sum
          (fun i : ℕ => f (blockElem (d := d) (k := k) (ℓ := ℓ) w i))) j := by
            apply congrArg (fun z : WK d k => blockElem (d := d) (k := k) (ℓ := ℓ) z j)
            rw [map_sum]
    _ = blockElem (d := d) (k := k) (ℓ := ℓ) ((Finset.range (k + 1)).sum
          (fun i : ℕ => (a ^ (k - i) * b ^ i) • blockElem (d := d) (k := k) (ℓ := ℓ) w i)) j := by
            apply congrArg (fun z : WK d k => blockElem (d := d) (k := k) (ℓ := ℓ) z j)
            apply Finset.sum_congr rfl
            intro i hi
            rw [map_scaleMap_twoScale_blockElem (d := d) (k := k) (ℓ := ℓ) (a := a) (b := b)
              (w := w) (j := i)]
    _ = (Finset.range (k + 1)).sum (fun i : ℕ =>
          (a ^ (k - i) * b ^ i) • blockElem (d := d) (k := k) (ℓ := ℓ)
            (blockElem (d := d) (k := k) (ℓ := ℓ) w i) j) := by
            rw [blockElem_sum]
    _ = (a ^ (k - j) * b ^ j) • blockElem (d := d) (k := k) (ℓ := ℓ) w j := by
          have hjmem : j ∈ Finset.range (k + 1) := by
            exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj)
          rw [Finset.sum_eq_single (s := Finset.range (k + 1)) (a := j)
            (f := fun i : ℕ => (a ^ (k - i) * b ^ i) • blockElem (d := d) (k := k) (ℓ := ℓ)
              (blockElem (d := d) (k := k) (ℓ := ℓ) w i) j)]
          · rw [blockElem_blockElem_idem (d := d) (k := k) (ℓ := ℓ) w]
          · intro i hi hneq
            have hcross := blockElem_blockElem_of_ne (d := d) (k := k) (ℓ := ℓ)
              (i := i) (j := j) (hij := hneq) w
            simp [hcross]
          · intro hnot
            exact (hnot hjmem).elim


/-- Squared norm of a block is at most the squared norm of the whole vector
(Pythagoras `Σⱼ ‖blockElem w j‖² = ‖w‖²`). -/
lemma normSq_blockElem_le_normSq {d k ℓ j : ℕ} (w : WK d k) (hj : j ≤ k) :
    ‖blockElem (d := d) (k := k) (ℓ := ℓ) w j‖ ^ 2 ≤ ‖w‖ ^ 2 := by
  classical
  have hsum := sum_normSq_blockElem (d := d) (k := k) (ℓ := ℓ) w
  rw [← hsum]
  exact Finset.single_le_sum
    (s := Finset.range (k + 1))
    (f := fun r : ℕ => ‖blockElem (d := d) (k := k) (ℓ := ℓ) w r‖ ^ 2)
    (by intro r hr; exact sq_nonneg _)
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))

/-- Norm of a block is at most the norm of the whole vector. -/
lemma norm_blockElem_le_norm {d k ℓ j : ℕ} (w : WK d k) (hj : j ≤ k) :
    ‖blockElem (d := d) (k := k) (ℓ := ℓ) w j‖ ≤ ‖w‖ := by
  have hsq := normSq_blockElem_le_normSq (d := d) (k := k) (ℓ := ℓ) w hj
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Norm of the flowed block equals the eigenvalue times the norm of the block, when the
scales are nonnegative (so the eigenvalue is nonnegative). -/
lemma norm_blockElem_map_twoScale {d k ℓ j : ℕ} (a b : ℝ) (w : WK d k) (hj : j ≤ k)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖blockElem (d := d) (k := k) (ℓ := ℓ)
        (exteriorPower.map k (scaleMap (twoScale a b ℓ)) w) j‖ =
      (a ^ (k - j) * b ^ j) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w j‖ := by
  rw [blockElem_map_scaleMap_twoScale (d := d) (k := k) (ℓ := ℓ) (a := a) (b := b) (w := w) (j := j) hj]
  rw [norm_smul]
  congr 1
  · rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (pow_nonneg ha _) (pow_nonneg hb _))]

variable {d k ℓ : ℕ}

lemma wcoord_eq_inner (w : WK d k) (s : IDX d k) :
    wcoord (d := d) (k := k) w s = inner ℝ (((Bk d k) s : WK d k)) w := by
  rw [wcoord]
  rw [OrthonormalBasis.repr_apply_apply]

def blockSubmodule (j : ℕ) : Submodule ℝ (WK d k) :=
  Submodule.span ℝ {e : WK d k |
    ∃ t : IDX d k, t ∈ blockFinset (d := d) (k := k) (ℓ := ℓ) j ∧ e = (Bk d k) t}

lemma blockElem_mem_blockSubmodule (j : ℕ) (w : WK d k) :
    blockElem (d := d) (k := k) (ℓ := ℓ) w j ∈ blockSubmodule (d := d) (k := k) (ℓ := ℓ) j := by
  classical
  have hgen : ∀ t ∈ blockFinset (d := d) (k := k) (ℓ := ℓ) j,
      ((Bk d k) t : WK d k) ∈ blockSubmodule (d := d) (k := k) (ℓ := ℓ) j := by
    intro t ht
    unfold blockSubmodule
    exact Submodule.subset_span ⟨t, ht, rfl⟩
  unfold blockElem
  exact Submodule.sum_mem (blockSubmodule (d := d) (k := k) (ℓ := ℓ) j)
    (by
      intro t ht
      exact Submodule.smul_mem (blockSubmodule (d := d) (k := k) (ℓ := ℓ) j)
        (wcoord (d := d) (k := k) w t) (hgen t ht))

lemma sub_blockElem_mem_orthogonal (j : ℕ) (w : WK d k) :
    w - blockElem (d := d) (k := k) (ℓ := ℓ) w j ∈ (blockSubmodule (d := d) (k := k) (ℓ := ℓ) j)ᗮ := by
  classical
  rw [Submodule.mem_orthogonal]
  intro z hz
  unfold blockSubmodule at hz
  refine Submodule.span_induction
    (p := fun (z : WK d k) (_ : z ∈ Submodule.span ℝ
      {e : WK d k | ∃ t : IDX d k, t ∈ blockFinset (d := d) (k := k) (ℓ := ℓ) j ∧ e = (Bk d k) t})
      => inner ℝ z (w - blockElem (d := d) (k := k) (ℓ := ℓ) w j) = 0) ?_ ?_ ?_ ?_ hz
  · rintro e he
    rcases he with ⟨t, ht, rfl⟩
    calc
      inner ℝ (((Bk d k) t : WK d k)) (w - blockElem (d := d) (k := k) (ℓ := ℓ) w j)
          = inner ℝ (((Bk d k) t : WK d k)) w -
            inner ℝ (((Bk d k) t : WK d k)) (blockElem (d := d) (k := k) (ℓ := ℓ) w j) := by
              rw [inner_sub_right]
      _ = wcoord (d := d) (k := k) w t - wcoord (d := d) (k := k)
            (blockElem (d := d) (k := k) (ℓ := ℓ) w j) t := by
            rw [wcoord_eq_inner w t]
            rw [wcoord_eq_inner (blockElem (d := d) (k := k) (ℓ := ℓ) w j) t]
      _ = 0 := by
            rw [wcoord_blockElem (d := d) (k := k) (ℓ := ℓ) (w := w) (s := t) (j := j)]
            rw [if_pos ht]
            ring
  · simp
  · intro a b ha hb hpa hpb
    simp [inner_add_left, hpa, hpb]
  · intro a x hx hpx
    simp [inner_smul_left, hpx]

lemma blockElem_eq_starProjection (j : ℕ) (w : WK d k) :
    (blockSubmodule (d := d) (k := k) (ℓ := ℓ) j).starProjection w =
      blockElem (d := d) (k := k) (ℓ := ℓ) w j := by
  classical
  apply Submodule.eq_starProjection_of_mem_orthogonal
    (K := blockSubmodule (d := d) (k := k) (ℓ := ℓ) j) (u := w)
    (v := blockElem (d := d) (k := k) (ℓ := ℓ) w j)
  · exact blockElem_mem_blockSubmodule (d := d) (k := k) (ℓ := ℓ) j w
  · exact sub_blockElem_mem_orthogonal (d := d) (k := k) (ℓ := ℓ) j w

end Submission.DiagonalFlow
