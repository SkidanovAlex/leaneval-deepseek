import Mathlib
import Submission.Work.LT.good_base_defs
import Submission.Work.LT.gb_card_preimage_submodule
import Submission.Work.LT.gb_rpow_exp_le
import Submission.Work.LT.gb_rpow_exp_le_one

set_option maxHeartbeats 1000000

namespace Work.LT

namespace GB

open scoped BigOperators

/-!
# Kalachev--Panteleev Lemma 4 (counting `H₁ x H₂ᵀ = 0`)

We count pairs of `r × D` matrices `(H₁,H₂)` over `𝔽₂` with `H₁ x H₂ᵀ = 0`, for a fixed matrix `x`
of rank at least `r`, and show that their number is at most `2^{2rD} · 2^{-r²/4}` out of the
`2^{2rD}` possible pairs.

The argument is a two-level count.  Writing `f = (v ↦ x v)` for the linear map given by `x`:

* for a fixed `H₂`, the valid `H₁` are exactly the `r`-tuples of elements of the subspace
  `W(H₂) = ⋂_{l} ker (w ↦ ⟨w, f (H₂ l)⟩)`, so there are `(2^{D - s(H₂)})^r` of them, where
  `s(H₂) = dim f(span (rows of H₂))`;
* splitting off one row of `H₂` at a time: adjoining `a` to a tuple whose `s` is `u` raises `s`
  to `u + 1` exactly when `f a ∉ f(span (rows so far))`, and the number of `a` with `f a` in a
  subspace `W` is `|ker f| · |W| = 2^{D-ρ} · 2^{u}`.  This gives the recursion
  `T(n+1) ≤ (2^{D-n-1} + (1-2^{-(n+1)}) 2^{D-ρ}) T(n)` for `T(n) = ∑_{H} 2^{-n s(H)}`, hence
  `T(r) ≤ ∏_{j=1}^{r} 2^{D-j+1} = 2^{rD - r(r-1)/2}`, which is enough since `r(r-1)/2 ≥ r²/4`
  for `r ≥ 2`.
-/

variable {D : ℕ}

/-! ## Duality for the dot pairing on `Fin D → ZMod 2` -/

lemma dotLin_single {D : ℕ} (u : Fin D → ZMod 2) (j : Fin D) :
    (dotLin u) (Pi.single j 1) = u j := by
  show dot u (Pi.single j 1) = u j
  rw [dot, Finset.sum_eq_single j]
  · simp
  · intro i _ hi; rw [Pi.single_eq_of_ne (show i ≠ j from hi), mul_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj

lemma dotLin_apply (u v : Fin D → ZMod 2) : (dotLin u) v = dot u v := rfl

lemma dotLin_injective : Function.Injective (dotLin (D := D)) := by
  intro u v huv
  funext j
  have h := congrFun (congrArg DFunLike.coe huv) (Pi.single j 1)
  rw [dotLin_single u j, dotLin_single v j] at h
  exact h

lemma sum_smul_single (w : Fin D → ZMod 2) :
    (∑ j : Fin D, w j • (Pi.single j (1 : ZMod 2) : Fin D → ZMod 2)) = w := by
  ext i
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.smul_apply, Pi.single_eq_of_ne (show i ≠ j from Ne.symm hj), smul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

lemma dotLin_surjective : Function.Surjective (dotLin (D := D)) := by
  intro φ
  refine ⟨fun j => φ (Pi.single j 1), ?_⟩
  refine LinearMap.ext fun w => ?_
  change (∑ i : Fin D, φ (Pi.single i 1) * w i) = φ w
  have hw : w = ∑ j : Fin D, w j • (Pi.single j (1 : ZMod 2) : Fin D → ZMod 2) :=
    (sum_smul_single w).symm
  conv_rhs => rw [hw]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  simp [smul_eq_mul, mul_comm]

/-- `dot` as a linear map in its first argument. -/
noncomputable def dotBilin (D : ℕ) :
    (Fin D → ZMod 2) →ₗ[ZMod 2] ((Fin D → ZMod 2) →ₗ[ZMod 2] ZMod 2) where
  toFun u := dotLin u
  map_add' u u' := by
    refine LinearMap.ext fun v => ?_
    change (∑ i, (u i + u' i) * v i) = (∑ i, u i * v i) + (∑ i, u' i * v i)
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => add_mul (u i) (u' i) (v i))]
    rw [Finset.sum_add_distrib]
  map_smul' c u := by
    refine LinearMap.ext fun v => ?_
    change (∑ i, (c * u i) * v i) = c * (∑ i, u i * v i)
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => mul_assoc c (u i) (v i))]
    rw [Finset.mul_sum]

/-- The duality `𝔽₂^D ≃ (𝔽₂^D)*` given by the dot pairing. -/
noncomputable def dotEquiv (D : ℕ) :
    (Fin D → ZMod 2) ≃ₗ[ZMod 2] ((Fin D → ZMod 2) →ₗ[ZMod 2] ZMod 2) :=
  LinearEquiv.ofBijective (dotBilin D) ⟨dotLin_injective, dotLin_surjective⟩

/-- Orthogonal complement of a subspace, for the standard dot pairing. -/
noncomputable def orth (W : Submodule (ZMod 2) (Fin D → ZMod 2)) :
    Submodule (ZMod 2) (Fin D → ZMod 2) :=
  W.dualAnnihilator.comap (dotEquiv D).toLinearMap

lemma mem_orth {W : Submodule (ZMod 2) (Fin D → ZMod 2)} {v : Fin D → ZMod 2} :
    v ∈ orth W ↔ ∀ w ∈ W, dot v w = 0 := by
  rw [orth, Submodule.mem_comap, Submodule.mem_dualAnnihilator]
  exact Iff.rfl

lemma finrank_orth (W : Submodule (ZMod 2) (Fin D → ZMod 2)) :
    Module.finrank (ZMod 2) (orth W) + Module.finrank (ZMod 2) W = D := by
  have hfin : Module.finrank (ZMod 2) (Fin D → ZMod 2) = D := by
    rw [Module.finrank_fintype_fun_eq_card]; simp
  have hmap : Submodule.map (dotEquiv D).toLinearMap (orth W) = W.dualAnnihilator := by
    rw [orth]
    exact Submodule.map_comap_eq_of_surjective (dotEquiv D).surjective W.dualAnnihilator
  have hfe : Module.finrank (ZMod 2) (orth W) = Module.finrank (ZMod 2) W.dualAnnihilator := by
    rw [← hmap]
    exact ((dotEquiv D).submoduleMap (orth W)).finrank_eq
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  rw [hfin] at h2
  omega

lemma card_orth (W : Submodule (ZMod 2) (Fin D → ZMod 2)) :
    Nat.card (orth W) = 2 ^ (D - Module.finrank (ZMod 2) W) := by
  have h := finrank_orth W
  have hcard : Nat.card ↥(orth W) = 2 ^ Module.finrank (ZMod 2) ↥(orth W) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(orth W)), Nat.card_zmod]
  rw [hcard]
  congr 1
  omega


/-! ## The matrix--vector map `v ↦ x v` -/

/-- The matrix `x` as a linear map `v ↦ x v`. -/
noncomputable def bpMatVecLin (x : Fin D × Fin D → ZMod 2) :
    (Fin D → ZMod 2) →ₗ[ZMod 2] (Fin D → ZMod 2) where
  toFun := matVec x
  map_add' v w := by
    refine funext fun i => ?_
    show (∑ j, x (i, j) * (v j + w j)) = (∑ j, x (i, j) * v j) + (∑ j, x (i, j) * w j)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  map_smul' c v := by
    refine funext fun i => ?_
    show (∑ j, x (i, j) * (c * v j)) = c * (∑ j, x (i, j) * v j)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring

lemma bpMatVecLin_apply (x : Fin D × Fin D → ZMod 2) (v : Fin D → ZMod 2) :
    bpMatVecLin x v = matVec x v := rfl

lemma matVec_eq_sum (x : Fin D × Fin D → ZMod 2) (v : Fin D → ZMod 2) :
    matVec x v = ∑ j : Fin D, v j • col x j := by
  funext i
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Pi.smul_apply, smul_eq_mul]
  simp only [matVec, col, mul_comm]

lemma matVec_single (x : Fin D × Fin D → ZMod 2) (j : Fin D) :
    bpMatVecLin x (Pi.single j 1) = col x j := by
  funext i
  show (∑ k, x (i, k) * (Pi.single j 1 : Fin D → ZMod 2) k) = x (i, j)
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk; rw [Pi.single_eq_of_ne hk, mul_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj

lemma range_bpMatVecLin (x : Fin D × Fin D → ZMod 2) :
    (bpMatVecLin x).range = colSpan x := by
  apply le_antisymm
  · rintro v ⟨w, rfl⟩
    rw [bpMatVecLin_apply, matVec_eq_sum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [colSpan, Submodule.span_le]
    rintro v ⟨j, rfl⟩
    exact ⟨Pi.single j 1, matVec_single x j⟩

lemma finrank_range_bpMatVecLin (x : Fin D × Fin D → ZMod 2) :
    Module.finrank (ZMod 2) (bpMatVecLin x).range = matRank x := by
  rw [range_bpMatVecLin]; rfl

lemma finrank_ker_bpMatVecLin (x : Fin D × Fin D → ZMod 2) :
    Module.finrank (ZMod 2) (bpMatVecLin x).ker = D - matRank x := by
  have hfin : Module.finrank (ZMod 2) (Fin D → ZMod 2) = D := by
    rw [Module.finrank_fintype_fun_eq_card]; simp
  have h := LinearMap.finrank_range_add_finrank_ker (bpMatVecLin x)
  rw [hfin, finrank_range_bpMatVecLin x] at h
  omega

lemma card_ker_bpMatVecLin (x : Fin D × Fin D → ZMod 2) :
    Nat.card ↥(bpMatVecLin x).ker = 2 ^ (D - matRank x) := by
  have hcard : Nat.card ↥(bpMatVecLin x).ker
      = 2 ^ Module.finrank (ZMod 2) ↥(bpMatVecLin x).ker := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(bpMatVecLin x).ker), Nat.card_zmod]
  rw [hcard, finrank_ker_bpMatVecLin x]


/-! ## Exponential helpers -/

lemma two_pow_add (a b : ℝ) : (2 : ℝ) ^ a * (2 : ℝ) ^ b = (2 : ℝ) ^ (a + b) :=
  (Real.rpow_add (by norm_num) a b).symm

lemma two_pow_pos (a : ℝ) : (0 : ℝ) < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a

lemma two_pow_le {a b : ℝ} (h : a ≤ b) : (2 : ℝ) ^ a ≤ (2 : ℝ) ^ b :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h

lemma natCast_two_pow (k : ℕ) : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ (k : ℝ) := by
  rw [Nat.cast_pow, show ((2 : ℕ) : ℝ) = (2 : ℝ) from by norm_num, ← Real.rpow_natCast]

/-! ## The counting argument -/

/-- Span of the vectors of a tuple. -/
noncomputable abbrev Uspan {D : ℕ} {n : ℕ} (H : Fin n → Fin D → ZMod 2) :
    Submodule (ZMod 2) (Fin D → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range H)

/-- Image under `v ↦ x v` of the span of the vectors of a tuple. -/
noncomputable abbrev Wimg (x : Fin D × Fin D → ZMod 2) {n : ℕ} (H : Fin n → Fin D → ZMod 2) :
    Submodule (ZMod 2) (Fin D → ZMod 2) :=
  Submodule.map (bpMatVecLin x) (Uspan H)

/-- `dim (x · span H)`. -/
noncomputable def sdim (x : Fin D × Fin D → ZMod 2) {n : ℕ} (H : Fin n → Fin D → ZMod 2) : ℕ :=
  Module.finrank (ZMod 2) (Wimg x H)

/-- `T n = ∑_{H : Fin n → 𝔽₂^D} 2^{-n · dim (x · span H)}`. -/
noncomputable def Tsum (x : Fin D × Fin D → ZMod 2) (n : ℕ) : ℝ :=
  ∑ H : Fin n → Fin D → ZMod 2, (2 : ℝ) ^ (-(n : ℝ) * (sdim x H : ℝ))

lemma Uspan_cons {n : ℕ} (a : Fin D → ZMod 2) (H : Fin n → Fin D → ZMod 2) :
    Uspan (Fin.cons a H) =
      Submodule.span (ZMod 2) ({a} : Set (Fin D → ZMod 2)) ⊔ Uspan H := by
  rw [Uspan, Uspan, Fin.range_cons, Submodule.span_insert]

lemma Wimg_cons {n : ℕ} (x : Fin D × Fin D → ZMod 2) (a : Fin D → ZMod 2)
    (H : Fin n → Fin D → ZMod 2) :
    Wimg x (Fin.cons a H) =
      Submodule.span (ZMod 2) ({bpMatVecLin x a} : Set (Fin D → ZMod 2)) ⊔ Wimg x H := by
  show Submodule.map (bpMatVecLin x) (Uspan (Fin.cons a H)) = _
  rw [Uspan_cons, Submodule.map_sup, Submodule.map_span, Set.image_singleton]

lemma span_singleton_le_iff {p : Submodule (ZMod 2) (Fin D → ZMod 2)} {v : Fin D → ZMod 2} :
    Submodule.span (ZMod 2) ({v} : Set (Fin D → ZMod 2)) ≤ p ↔ v ∈ p :=
  Submodule.span_singleton_le_iff_mem v p

lemma sdim_cons_of_mem {n : ℕ} (x : Fin D × Fin D → ZMod 2) (a : Fin D → ZMod 2)
    (H : Fin n → Fin D → ZMod 2) (h : bpMatVecLin x a ∈ Wimg x H) :
    sdim x (Fin.cons a H) = sdim x H := by
  have hsup : Submodule.span (ZMod 2) ({bpMatVecLin x a} : Set (Fin D → ZMod 2)) ⊔ Wimg x H
      = Wimg x H := sup_eq_right.mpr (span_singleton_le_iff.mpr h)
  show Module.finrank (ZMod 2) (Wimg x (Fin.cons a H)) = Module.finrank (ZMod 2) (Wimg x H)
  rw [Wimg_cons, hsup]

lemma sdim_cons_of_notMem {n : ℕ} (x : Fin D × Fin D → ZMod 2) (a : Fin D → ZMod 2)
    (H : Fin n → Fin D → ZMod 2) (h : bpMatVecLin x a ∉ Wimg x H) :
    sdim x (Fin.cons a H) = sdim x H + 1 := by
  have h2 : Module.finrank (ZMod 2)
        ↥(Submodule.span (ZMod 2) ({bpMatVecLin x a} : Set (Fin D → ZMod 2)) ⊔ Wimg x H)
      = Module.finrank (ZMod 2) ↥(Wimg x H) + 1 := by
    rw [sup_comm]
    exact Submodule.finrank_sup_span_singleton (p := Wimg x H) h
  show Module.finrank (ZMod 2) (Wimg x (Fin.cons a H)) = Module.finrank (ZMod 2) (Wimg x H) + 1
  rw [Wimg_cons, h2]

lemma sdim_le (x : Fin D × Fin D → ZMod 2) {n : ℕ} (H : Fin n → Fin D → ZMod 2) :
    sdim x H ≤ D := by
  have hfin : Module.finrank (ZMod 2) (Fin D → ZMod 2) = D := by
    rw [Module.finrank_fintype_fun_eq_card]; simp
  have h := Submodule.finrank_le (Wimg x H)
  rw [hfin] at h
  exact h

lemma matRank_le (x : Fin D × Fin D → ZMod 2) : matRank x ≤ D := by
  have hfin : Module.finrank (ZMod 2) (Fin D → ZMod 2) = D := by
    rw [Module.finrank_fintype_fun_eq_card]; simp
  have h := Submodule.finrank_le (bpMatVecLin x).range
  rw [hfin, finrank_range_bpMatVecLin x] at h
  exact h

lemma natCard_submodule (W : Submodule (ZMod 2) (Fin D → ZMod 2)) :
    Nat.card ↥W = 2 ^ Module.finrank (ZMod 2) ↥W := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥W), Nat.card_zmod]

lemma natCard_V : Nat.card (Fin D → ZMod 2) = 2 ^ D := by
  rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]

lemma Wimg_eq_span (x : Fin D × Fin D → ZMod 2) {n : ℕ} (H : Fin n → Fin D → ZMod 2) :
    Wimg x H = Submodule.span (ZMod 2)
      (Set.range (fun l : Fin n => matVec x (H l))) := by
  show Submodule.map (bpMatVecLin x) (Submodule.span (ZMod 2) (Set.range H)) = _
  rw [Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨u, ⟨l, rfl⟩, rfl⟩
    exact ⟨l, rfl⟩
  · rintro ⟨l, rfl⟩
    exact ⟨H l, ⟨l, rfl⟩, rfl⟩

lemma mem_orth_span_range {n : ℕ} {z : Fin n → Fin D → ZMod 2} {v : Fin D → ZMod 2} :
    v ∈ orth (Submodule.span (ZMod 2) (Set.range z)) ↔ ∀ l, dot v (z l) = 0 := by
  rw [mem_orth]
  constructor
  · intro h l; exact h (z l) (Submodule.subset_span ⟨l, rfl⟩)
  · intro h
    have hle : Submodule.span (ZMod 2) (Set.range z) ≤ LinearMap.ker (dotLin v) :=
      Submodule.span_le.mpr (fun y hy => by
        rcases hy with ⟨l, rfl⟩
        exact LinearMap.mem_ker.mpr (by simpa only [dotLin_apply] using h l))
    intro w hw
    have h2 : w ∈ LinearMap.ker (dotLin v) := hle hw
    have h3 := LinearMap.mem_ker.mp h2
    simpa only [dotLin_apply] using h3

lemma pairCond_iff_mem_orth {r : ℕ} (x : Fin D × Fin D → ZMod 2)
    (H1 H2 : Fin r → Fin D → ZMod 2) :
    pairCond H1 H2 x ↔ ∀ l, H1 l ∈ orth (Wimg x H2) := by
  rw [Wimg_eq_span]
  constructor
  · intro h l
    exact mem_orth_span_range.mpr (fun l' => h l l')
  · intro h k l
    exact (mem_orth_span_range.mp (h k)) l

lemma Wimg_le_range (x : Fin D × Fin D → ZMod 2) {n : ℕ} (H : Fin n → Fin D → ZMod 2) :
    Wimg x H ≤ (bpMatVecLin x).range := by
  intro v hv
  rw [Wimg, Submodule.mem_map] at hv
  obtain ⟨u, -, rfl⟩ := hv
  exact LinearMap.mem_range.mpr ⟨u, rfl⟩

lemma sdim_le_matRank (x : Fin D × Fin D → ZMod 2) {n : ℕ} (H : Fin n → Fin D → ZMod 2) :
    sdim x H ≤ matRank x := by
  have h := Submodule.finrank_mono (Wimg_le_range x H)
  rwa [finrank_range_bpMatVecLin x] at h

/-- For fixed `H₂ = H`, the number of valid `H₁` is `|orth (Wimg x H)|^r`. -/
lemma card_fixed (x : Fin D × Fin D → ZMod 2) (r : ℕ) (H : Fin r → Fin D → ZMod 2) :
    Nat.card {H1 : Fin r → Fin D → ZMod 2 // pairCond H1 H x} =
      (Nat.card (orth (Wimg x H))) ^ r := by
  have h1 : Nat.card {H1 : Fin r → Fin D → ZMod 2 // pairCond H1 H x}
      = Nat.card {H1 : Fin r → Fin D → ZMod 2 // ∀ l, H1 l ∈ orth (Wimg x H)} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun H1 => pairCond_iff_mem_orth x H1 H))
  have h2 : Nat.card {H1 : Fin r → Fin D → ZMod 2 // ∀ l, H1 l ∈ orth (Wimg x H)}
      = Nat.card ((l : Fin r) → {v : Fin D → ZMod 2 // v ∈ orth (Wimg x H)}) :=
    Nat.card_congr (Equiv.subtypePiEquivPi
      (β := fun _ : Fin r => (Fin D → ZMod 2)) (p := fun _ v => v ∈ orth (Wimg x H)))
  rw [h1, h2, Nat.card_fun, Nat.card_fin]

/-- The double count: summing the fibres over the first, resp. second, coordinate. -/
lemma sum_fiber_comm (x : Fin D × Fin D → ZMod 2) (r : ℕ) :
    (∑ a : Fin r → Fin D → ZMod 2,
        Nat.card {b : Fin r → Fin D → ZMod 2 // pairCond a b x})
      = ∑ b : Fin r → Fin D → ZMod 2,
          Nat.card {a : Fin r → Fin D → ZMod 2 // pairCond a b x} := by
  have he1 : Nat.card {p : (Fin r → Fin D → ZMod 2) × (Fin r → Fin D → ZMod 2) //
        pairCond p.1 p.2 x}
      = ∑ a : Fin r → Fin D → ZMod 2,
          Nat.card {b : Fin r → Fin D → ZMod 2 // pairCond a b x} := by
    rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun a b => pairCond a b x)),
      Nat.card_sigma]
  have htot : Nat.card {p : (Fin r → Fin D → ZMod 2) × (Fin r → Fin D → ZMod 2) //
        pairCond p.1 p.2 x}
      = ∑ b : Fin r → Fin D → ZMod 2,
          Nat.card {a : Fin r → Fin D → ZMod 2 // pairCond a b x} := by
    have h1 : Nat.card {p : (Fin r → Fin D → ZMod 2) × (Fin r → Fin D → ZMod 2) //
          pairCond p.1 p.2 x}
        = Nat.card {p : (Fin r → Fin D → ZMod 2) × (Fin r → Fin D → ZMod 2) //
          pairCond p.2 p.1 x} :=
      Nat.card_congr (Equiv.subtypeEquiv (Equiv.prodComm _ _)
        (p := fun p => pairCond p.1 p.2 x) (q := fun p => pairCond p.2 p.1 x)
        (fun p => Iff.rfl))
    rw [h1, Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun b a => pairCond a b x)),
      Nat.card_sigma]
  exact he1.symm.trans htot

/-- The total number of pairs, split according to `H₂`. -/
lemma card_pairs_eq (x : Fin D × Fin D → ZMod 2) (r : ℕ) :
    Nat.card {p : (Fin r → Fin D → ZMod 2) × (Fin r → Fin D → ZMod 2) // pairCond p.1 p.2 x}
      = ∑ H : Fin r → Fin D → ZMod 2, (Nat.card (orth (Wimg x H))) ^ r := by
  have h1 : Nat.card {p : (Fin r → Fin D → ZMod 2) × (Fin r → Fin D → ZMod 2) //
        pairCond p.1 p.2 x}
      = ∑ H : Fin r → Fin D → ZMod 2,
          Nat.card {H1 : Fin r → Fin D → ZMod 2 // pairCond H1 H x} := by
    rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun a b => pairCond a b x)),
      Nat.card_sigma, sum_fiber_comm x r]
  rw [h1]
  exact Finset.sum_congr rfl (fun H _ => card_fixed x r H)

/-- Cardinality of `orth (Wimg x H)` as a real number. -/
lemma card_orth_val (x : Fin D × Fin D → ZMod 2) {n : ℕ} (H : Fin n → Fin D → ZMod 2) :
    (Nat.card (orth (Wimg x H)) : ℝ) = (2 : ℝ) ^ ((D : ℝ) - (sdim x H : ℝ)) := by
  have hs : Module.finrank (ZMod 2) (Wimg x H) ≤ D := sdim_le x H
  rw [card_orth, sdim]
  push_cast
  rw [← Real.rpow_natCast, Nat.cast_sub hs]

/-- The exact splitting of one row off the tuple. -/
lemma fiber_eq (x : Fin D × Fin D → ZMod 2) {n : ℕ} (H : Fin n → Fin D → ZMod 2) :
    (∑ a : Fin D → ZMod 2, (2 : ℝ) ^ (-((n : ℝ) + 1) * (sdim x (Fin.cons a H) : ℝ))) =
      (Nat.card {a : Fin D → ZMod 2 // bpMatVecLin x a ∈ Wimg x H} : ℝ) *
          (2 : ℝ) ^ (-((n : ℝ) + 1) * (sdim x H : ℝ)) +
        ((2 : ℝ) ^ ((D : ℝ)) -
            (Nat.card {a : Fin D → ZMod 2 // bpMatVecLin x a ∈ Wimg x H} : ℝ)) *
          (2 : ℝ) ^ (-((n : ℝ) + 1) * ((sdim x H : ℝ) + 1)) := by
  classical
  set p : (Fin D → ZMod 2) → Prop := fun a => bpMatVecLin x a ∈ Wimg x H with hp
  have hkey : ∀ a : Fin D → ZMod 2,
      (2 : ℝ) ^ (-((n : ℝ) + 1) * (sdim x (Fin.cons a H) : ℝ)) =
        (if p a then (2 : ℝ) ^ (-((n : ℝ) + 1) * (sdim x H : ℝ))
          else (2 : ℝ) ^ (-((n : ℝ) + 1) * ((sdim x H : ℝ) + 1))) := by
    intro a
    by_cases h : p a
    · rw [if_pos h, sdim_cons_of_mem x a H h]
    · rw [if_neg h, sdim_cons_of_notMem x a H h]
      congr 1
      push_cast
      ring
  rw [Finset.sum_congr rfl (fun a _ => hkey a), Finset.sum_ite, Finset.sum_const,
    Finset.sum_const]
  have hA : ((Finset.univ.filter p).card : ℝ) = (Nat.card {a // p a} : ℝ) := by
    congr 1
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_ofFinset (p := {a | p a}) (Finset.univ.filter p)
      (fun x => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq])).symm
  have hle : (Finset.univ.filter p).card ≤ (Finset.univ : Finset (Fin D → ZMod 2)).card :=
    Finset.card_filter_le _ _
  have hB : ((Finset.univ.filter (fun a => ¬ p a)).card : ℝ) =
      (2 : ℝ) ^ ((D : ℝ)) - (Nat.card {a // p a} : ℝ) := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin D → ZMod 2))) p
    have huniv : ((Finset.univ : Finset (Fin D → ZMod 2)).card : ℝ) = (2 : ℝ) ^ ((D : ℝ)) := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, natCard_V, natCast_two_pow]
    have hc : ((Finset.univ : Finset (Fin D → ZMod 2)).card : ℝ) =
        ((Finset.univ.filter p).card : ℝ) + ((Finset.univ.filter (fun a => ¬ p a)).card : ℝ) := by
      rw [← Nat.cast_add, h]
    rw [huniv, hA] at hc
    rw [hc]
    ring
  rw [nsmul_eq_mul, nsmul_eq_mul, hA, hB]

/-- The fibre bound: at most `2^{D-ρ} + 2^{D-n-1}` times the term with exponent `n`. -/
lemma fiber_le (x : Fin D × Fin D → ZMod 2) {n : ℕ} (H : Fin n → Fin D → ZMod 2) :
    (∑ a : Fin D → ZMod 2, (2 : ℝ) ^ (-((n : ℝ) + 1) * (sdim x (Fin.cons a H) : ℝ))) ≤
      ((2 : ℝ) ^ ((D : ℝ) - (matRank x : ℝ)) + (2 : ℝ) ^ ((D : ℝ) - (n : ℝ) - 1)) *
        (2 : ℝ) ^ (-(n : ℝ) * (sdim x H : ℝ)) := by
  have hs : sdim x H ≤ D := sdim_le x H
  have hρ : matRank x ≤ D := matRank_le x
  have hX : (0 : ℝ) < (2 : ℝ) ^ (-((n : ℝ) + 1) * (sdim x H : ℝ)) := two_pow_pos _
  have hY : (0 : ℝ) < (2 : ℝ) ^ (-((n : ℝ) + 1) * ((sdim x H : ℝ) + 1)) := two_pow_pos _
  have hA : (Nat.card {a : Fin D → ZMod 2 // bpMatVecLin x a ∈ Wimg x H} : ℝ)
      ≤ (2 : ℝ) ^ ((D : ℝ) - (matRank x : ℝ)) * (2 : ℝ) ^ (sdim x H : ℝ) := by
    have hpre := gb_card_preimage_submodule (bpMatVecLin x) (Wimg x H) (Wimg_le_range x H)
    rw [hpre, card_ker_bpMatVecLin x, natCard_submodule (Wimg x H), sdim]
    simp only [Nat.cast_mul]
    rw [natCast_two_pow, natCast_two_pow, Nat.cast_sub hρ]
  have hAD : (Nat.card {a : Fin D → ZMod 2 // bpMatVecLin x a ∈ Wimg x H} : ℝ)
      ≤ (2 : ℝ) ^ ((D : ℝ)) := by
    calc (Nat.card {a : Fin D → ZMod 2 // bpMatVecLin x a ∈ Wimg x H} : ℝ)
        ≤ ((2 : ℝ) ^ ((D : ℝ) - (matRank x : ℝ)) * (2 : ℝ) ^ (sdim x H : ℝ)) := hA
      _ = (2 : ℝ) ^ ((D : ℝ) - (matRank x : ℝ) + (sdim x H : ℝ)) := two_pow_add _ _
      _ ≤ (2 : ℝ) ^ ((D : ℝ)) := by
          apply two_pow_le
          have h1 : (0 : ℝ) ≤ (sdim x H : ℝ) := Nat.cast_nonneg _
          have h2 : (matRank x : ℝ) ≤ (D : ℝ) := Nat.cast_le.mpr hρ
          have h3 : (sdim x H : ℝ) ≤ (matRank x : ℝ) :=
            Nat.cast_le.mpr (sdim_le_matRank x H)
          linarith
  rw [fiber_eq x H]
  calc (Nat.card {a : Fin D → ZMod 2 // bpMatVecLin x a ∈ Wimg x H} : ℝ) *
          (2 : ℝ) ^ (-((n : ℝ) + 1) * (sdim x H : ℝ)) +
        ((2 : ℝ) ^ ((D : ℝ)) -
            (Nat.card {a : Fin D → ZMod 2 // bpMatVecLin x a ∈ Wimg x H} : ℝ)) *
          (2 : ℝ) ^ (-((n : ℝ) + 1) * ((sdim x H : ℝ) + 1))
      ≤ ((2 : ℝ) ^ ((D : ℝ) - (matRank x : ℝ)) * (2 : ℝ) ^ (sdim x H : ℝ)) *
            (2 : ℝ) ^ (-((n : ℝ) + 1) * (sdim x H : ℝ)) +
          (2 : ℝ) ^ ((D : ℝ)) *
            (2 : ℝ) ^ (-((n : ℝ) + 1) * ((sdim x H : ℝ) + 1)) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hA (le_of_lt hX)
        · exact mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hY)
      _ ≤ ((2 : ℝ) ^ ((D : ℝ) - (matRank x : ℝ)) + (2 : ℝ) ^ ((D : ℝ) - (n : ℝ) - 1)) *
            (2 : ℝ) ^ (-(n : ℝ) * (sdim x H : ℝ)) := by
        rw [add_mul]
        simp only [two_pow_add]
        apply add_le_add
        · apply two_pow_le
          have h1 : (0 : ℝ) ≤ (sdim x H : ℝ) := Nat.cast_nonneg _
          nlinarith
        · apply two_pow_le
          have h1 : (0 : ℝ) ≤ (sdim x H : ℝ) := Nat.cast_nonneg _
          nlinarith

/-- `Tsum` in terms of the sums over the last row. -/
lemma Tsum_succ_eq (x : Fin D × Fin D → ZMod 2) (n : ℕ) :
    Tsum x (n + 1) =
      ∑ H : Fin n → Fin D → ZMod 2, ∑ a : Fin D → ZMod 2,
        (2 : ℝ) ^ (-((n : ℝ) + 1) * (sdim x (Fin.cons a H) : ℝ)) := by
  unfold Tsum
  simp only [Nat.cast_add, Nat.cast_one]
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => (Fin D → ZMod 2)))
    (fun p : (Fin D → ZMod 2) × (Fin n → Fin D → ZMod 2) =>
      (2 : ℝ) ^ (-((n : ℝ) + 1) * (sdim x (Fin.cons p.1 p.2) : ℝ)))
    (fun G : Fin (n + 1) → Fin D → ZMod 2 =>
      (2 : ℝ) ^ (-((n : ℝ) + 1) * (sdim x G : ℝ)))
    (fun p => rfl)]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma Tsum_zero (x : Fin D × Fin D → ZMod 2) : Tsum x 0 = 1 := by
  rw [Tsum]
  simp

/-- One step of the recursion for `Tsum`. -/
lemma Tsum_succ_le (x : Fin D × Fin D → ZMod 2) (n : ℕ) :
    Tsum x (n + 1) ≤
      ((2 : ℝ) ^ ((D : ℝ) - (matRank x : ℝ)) + (2 : ℝ) ^ ((D : ℝ) - (n : ℝ) - 1)) *
        Tsum x n := by
  rw [Tsum_succ_eq]
  calc ∑ H : Fin n → Fin D → ZMod 2, ∑ a : Fin D → ZMod 2,
        (2 : ℝ) ^ (-((n : ℝ) + 1) * (sdim x (Fin.cons a H) : ℝ))
      ≤ ∑ H : Fin n → Fin D → ZMod 2,
          ((2 : ℝ) ^ ((D : ℝ) - (matRank x : ℝ)) + (2 : ℝ) ^ ((D : ℝ) - (n : ℝ) - 1)) *
            (2 : ℝ) ^ (-(n : ℝ) * (sdim x H : ℝ)) :=
        Finset.sum_le_sum (fun H _ => fiber_le x H)
      _ = ((2 : ℝ) ^ ((D : ℝ) - (matRank x : ℝ)) + (2 : ℝ) ^ ((D : ℝ) - (n : ℝ) - 1)) *
            Tsum x n := by
        rw [Tsum, Finset.mul_sum]

lemma Tsum_nonneg (x : Fin D × Fin D → ZMod 2) (n : ℕ) : 0 ≤ Tsum x n := by
  rw [Tsum]
  exact Finset.sum_nonneg (fun H _ => le_of_lt (two_pow_pos _))

lemma Tsum_one_le_pow (x : Fin D × Fin D → ZMod 2) (hr : 1 ≤ matRank x) :
    Tsum x 1 ≤ (2 : ℝ) ^ ((D : ℝ)) := by
  have hstep := Tsum_succ_le x 0
  rw [Tsum_zero, mul_one] at hstep
  refine hstep.trans ?_
  have h1 : (2 : ℝ) ^ ((D : ℝ) - (matRank x : ℝ)) ≤ (2 : ℝ) ^ ((D : ℝ) - 1) := by
    apply two_pow_le
    have : (1 : ℝ) ≤ (matRank x : ℝ) := by exact_mod_cast hr
    linarith
  calc (2 : ℝ) ^ ((D : ℝ) - (matRank x : ℝ)) + (2 : ℝ) ^ ((D : ℝ) - ((0 : ℕ) : ℝ) - 1)
      ≤ (2 : ℝ) ^ ((D : ℝ) - 1) + (2 : ℝ) ^ ((D : ℝ) - 1) := by
        rw [Nat.cast_zero, sub_zero]
        exact add_le_add h1 le_rfl
    _ = (2 : ℝ) ^ ((D : ℝ)) := by
        rw [show (2 : ℝ) ^ ((D : ℝ) - 1) + (2 : ℝ) ^ ((D : ℝ) - 1)
            = 2 * (2 : ℝ) ^ ((D : ℝ) - 1) from by ring]
        rw [show 2 * (2 : ℝ) ^ ((D : ℝ) - 1)
            = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ ((D : ℝ) - 1) from by
              rw [Real.rpow_one]]
        rw [two_pow_add]
        congr 1
        ring

/-- The crude product bound, valid for `n ≥ 2`. -/
lemma Tsum_le (x : Fin D × Fin D → ZMod 2) :
    ∀ n : ℕ, 2 ≤ n → n ≤ matRank x →
      Tsum x n ≤ (2 : ℝ) ^ ((n : ℝ) * (D : ℝ) - (n : ℝ) * ((n : ℝ) - 1) / 2) := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by omega)
  | succ k ih =>
    intro h2 hk
    have hle : k ≤ matRank x := le_trans (Nat.le_succ k) hk
    have hstep := Tsum_succ_le x k
    have hfact : ((2 : ℝ) ^ ((D : ℝ) - (matRank x : ℝ)) + (2 : ℝ) ^ ((D : ℝ) - (k : ℝ) - 1))
        ≤ (2 : ℝ) ^ ((D : ℝ) - (k : ℝ)) := by
      have hρ : (k : ℝ) + 1 ≤ (matRank x : ℝ) := by exact_mod_cast hk
      have h1 : (2 : ℝ) ^ ((D : ℝ) - (matRank x : ℝ)) ≤ (2 : ℝ) ^ ((D : ℝ) - (k : ℝ) - 1) := by
        apply two_pow_le; linarith
      calc (2 : ℝ) ^ ((D : ℝ) - (matRank x : ℝ)) + (2 : ℝ) ^ ((D : ℝ) - (k : ℝ) - 1)
          ≤ (2 : ℝ) ^ ((D : ℝ) - (k : ℝ) - 1) + (2 : ℝ) ^ ((D : ℝ) - (k : ℝ) - 1) := by
            linarith
        _ = (2 : ℝ) ^ ((D : ℝ) - (k : ℝ)) := by
            rw [show (2 : ℝ) ^ ((D : ℝ) - (k : ℝ) - 1) + (2 : ℝ) ^ ((D : ℝ) - (k : ℝ) - 1)
                = 2 * (2 : ℝ) ^ ((D : ℝ) - (k : ℝ) - 1) from by ring]
            rw [show 2 * (2 : ℝ) ^ ((D : ℝ) - (k : ℝ) - 1)
                = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ ((D : ℝ) - (k : ℝ) - 1) from by
                  rw [Real.rpow_one]]
            rw [two_pow_add]
            congr 1
            ring
    have hIH : Tsum x k ≤ (2 : ℝ) ^ ((k : ℝ) * (D : ℝ) - (k : ℝ) * ((k : ℝ) - 1) / 2) := by
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · have hk1 : k = 1 := by omega
        subst hk1
        exact (Tsum_one_le_pow x (by omega : 1 ≤ matRank x)).trans (le_of_eq (by
          congr 1
          push_cast
          ring))
      · exact ih hk2 hle
    have hfinal : (2 : ℝ) ^ ((D : ℝ) - (k : ℝ)) *
          (2 : ℝ) ^ ((k : ℝ) * (D : ℝ) - (k : ℝ) * ((k : ℝ) - 1) / 2)
        = (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * (D : ℝ) -
            ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) - 1) / 2) := by
      rw [two_pow_add]
      congr 1
      push_cast
      ring
    calc Tsum x (k + 1) ≤ ((2 : ℝ) ^ ((D : ℝ) - (matRank x : ℝ)) +
            (2 : ℝ) ^ ((D : ℝ) - (k : ℝ) - 1)) * Tsum x k := hstep
      _ ≤ (2 : ℝ) ^ ((D : ℝ) - (k : ℝ)) * Tsum x k :=
          mul_le_mul_of_nonneg_right hfact (Tsum_nonneg x k)
      _ ≤ (2 : ℝ) ^ ((D : ℝ) - (k : ℝ)) *
            (2 : ℝ) ^ ((k : ℝ) * (D : ℝ) - (k : ℝ) * ((k : ℝ) - 1) / 2) :=
          mul_le_mul_of_nonneg_left hIH (le_of_lt (two_pow_pos _))
      _ = (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * (D : ℝ) -
            ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) - 1) / 2) := hfinal

/-- The sharp bound for `n = 1`: the factor `2^{D-1} + 2^{-1}2^{D-ρ}` is at most `3·2^{D-2}`. -/
lemma Tsum_one_le (x : Fin D × Fin D → ZMod 2) (hr : 1 ≤ matRank x) :
    Tsum x 1 ≤ (3 : ℝ) * (2 : ℝ) ^ ((D : ℝ) - 2) := by
  have hempty : (Set.range (Fin.elim0 : Fin 0 → Fin D → ZMod 2)) = ∅ := by
    ext v
    simp
  have hbot : Wimg x (Fin.elim0 : Fin 0 → Fin D → ZMod 2) = ⊥ := by
    show Submodule.map (bpMatVecLin x) (Uspan (Fin.elim0 : Fin 0 → Fin D → ZMod 2)) = ⊥
    rw [Uspan, hempty, Submodule.span_empty, Submodule.map_bot]
  have hs0 : sdim x (Fin.elim0 : Fin 0 → Fin D → ZMod 2) = 0 := by
    rw [sdim, hbot]
    exact finrank_bot (ZMod 2) (Fin D → ZMod 2)
  have hA : (Nat.card {a : Fin D → ZMod 2 //
        bpMatVecLin x a ∈ Wimg x (Fin.elim0 : Fin 0 → Fin D → ZMod 2)} : ℝ)
      = (2 : ℝ) ^ ((D : ℝ) - (matRank x : ℝ)) := by
    have hpre := gb_card_preimage_submodule (bpMatVecLin x)
      (Wimg x (Fin.elim0 : Fin 0 → Fin D → ZMod 2)) (Wimg_le_range x _)
    have hW : Nat.card ↥(Wimg x (Fin.elim0 : Fin 0 → Fin D → ZMod 2)) = 1 := by
      rw [natCard_submodule, hbot, finrank_bot, pow_zero]
    rw [hpre, card_ker_bpMatVecLin x, hW, mul_one, natCast_two_pow, Nat.cast_sub (matRank_le x)]
  have hT : Tsum x 1 = ∑ a : Fin D → ZMod 2,
      (2 : ℝ) ^ (-(((0 : ℕ) : ℝ) + 1) *
        (sdim x (Fin.cons a (Fin.elim0 : Fin 0 → Fin D → ZMod 2)) : ℝ)) := by
    rw [Tsum_succ_eq x 0, Fintype.sum_subsingleton _
      (Fin.elim0 : Fin 0 → Fin D → ZMod 2)]
  have hfib := fiber_eq x (H := (Fin.elim0 : Fin 0 → Fin D → ZMod 2))
  have hX : (2 : ℝ) ^ (-(((0 : ℕ) : ℝ) + 1) * (sdim x (Fin.elim0 : Fin 0 → _) : ℝ)) = 1 := by
    rw [hs0, Nat.cast_zero, mul_zero, Real.rpow_zero]
  have hY : (2 : ℝ) ^ (-(((0 : ℕ) : ℝ) + 1) * ((sdim x (Fin.elim0 : Fin 0 → _) : ℝ) + 1))
      = (1 / 2 : ℝ) := by
    rw [hs0, show -(((0 : ℕ) : ℝ) + 1) * (((0 : ℕ) : ℝ) + 1) = (-1 : ℝ) from by norm_num,
      Real.rpow_neg_one]
    norm_num
  rw [hT, hfib, hA, hX, hY]
  have hr1 : (1 : ℝ) ≤ (matRank x : ℝ) := by exact_mod_cast hr
  have hkey : (2 : ℝ) ^ ((D : ℝ) - (matRank x : ℝ) - 1) ≤ (2 : ℝ) ^ ((D : ℝ) - 2) := by
    apply two_pow_le; linarith
  have hpow1 : (2 : ℝ) ^ ((D : ℝ) - (matRank x : ℝ)) * (1 / 2)
      = (2 : ℝ) ^ ((D : ℝ) - (matRank x : ℝ) - 1) := by
    have he : ((D : ℝ) - (matRank x : ℝ)) + (-1) = (D : ℝ) - (matRank x : ℝ) - 1 := by ring
    rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) from by rw [Real.rpow_neg_one]; norm_num,
      two_pow_add, he]
  have hpow2 : (2 : ℝ) ^ ((D : ℝ)) * (1 / 2) = (2 : ℝ) ^ ((D : ℝ) - 1) := by
    have he : (D : ℝ) + (-1) = (D : ℝ) - 1 := by ring
    rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) from by rw [Real.rpow_neg_one]; norm_num,
      two_pow_add, he]
  have hpow3 : 2 * (2 : ℝ) ^ ((D : ℝ) - 2) = (2 : ℝ) ^ ((D : ℝ) - 1) := by
    have he : (1 : ℝ) + ((D : ℝ) - 2) = (D : ℝ) - 1 := by ring
    rw [show 2 * (2 : ℝ) ^ ((D : ℝ) - 2)
        = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ ((D : ℝ) - 2) from by rw [Real.rpow_one],
      two_pow_add, he]
  calc (2 : ℝ) ^ ((D : ℝ) - (matRank x : ℝ)) * 1 +
        ((2 : ℝ) ^ ((D : ℝ)) - (2 : ℝ) ^ ((D : ℝ) - (matRank x : ℝ))) * (1 / 2)
      = (2 : ℝ) ^ ((D : ℝ) - (matRank x : ℝ)) * (1 / 2) + (2 : ℝ) ^ ((D : ℝ)) * (1 / 2) := by
        ring
    _ = (2 : ℝ) ^ ((D : ℝ) - (matRank x : ℝ) - 1) + (2 : ℝ) ^ ((D : ℝ) - 1) := by
        rw [hpow1, hpow2]
    _ ≤ (2 : ℝ) ^ ((D : ℝ) - 2) + 2 * (2 : ℝ) ^ ((D : ℝ) - 2) := by
        rw [hpow3]
        linarith
    _ = 3 * (2 : ℝ) ^ ((D : ℝ) - 2) := by ring

end GB

/-- Kalachev--Panteleev Lemma 4, in the "kernel of a random parity-check matrix" model: for a fixed matrix `x` of rank at least `r`, the number of pairs of `r × D` matrices `(H₁,H₂)` with `H₁ x H₂ᵀ = 0` (that is, `pairCond H₁ H₂ x`) is at most `2^{2 r D - r²/4}`, where `2^{2rD}` is the total number of pairs. -/
theorem gb_card_bad_pair {D r : ℕ} (x : Fin D × Fin D → ZMod 2) (hr : r ≤ GB.matRank x) :
    (Nat.card {p : (Fin r → Fin D → ZMod 2) × (Fin r → Fin D → ZMod 2) //
      GB.pairCond p.1 p.2 x} : ℝ) ≤
      (2 : ℝ) ^ (2 * r * D) * (2 : ℝ) ^ (-(r : ℝ) ^ 2 / 4) := by
  have hA : (Nat.card {p : (Fin r → Fin D → ZMod 2) × (Fin r → Fin D → ZMod 2) //
        GB.pairCond p.1 p.2 x} : ℝ)
      = (2 : ℝ) ^ ((r : ℝ) * (D : ℝ)) * GB.Tsum x r := by
    rw [GB.card_pairs_eq x r, Nat.cast_sum, GB.Tsum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro H _
    rw [Nat.cast_pow, GB.card_orth_val x H]
    calc ((2 : ℝ) ^ ((D : ℝ) - (GB.sdim x H : ℝ))) ^ r
        = (2 : ℝ) ^ ((r : ℝ) * ((D : ℝ) - (GB.sdim x H : ℝ))) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          congr 1
          ring
      _ = (2 : ℝ) ^ ((r : ℝ) * (D : ℝ)) *
            (2 : ℝ) ^ (-(r : ℝ) * (GB.sdim x H : ℝ)) := by
          rw [GB.two_pow_add]
          congr 1
          ring
  rcases Nat.lt_or_ge r 2 with hr2 | hr2
  · have h01 : r = 0 ∨ r = 1 := by omega
    rcases h01 with rfl | rfl
    · -- r = 0
      rw [hA]
      simp [GB.Tsum, GB.sdim]
    · -- r = 1
      have hD : 1 ≤ D := by have h := GB.matRank_le x; omega
      have h1 : GB.Tsum x 1 ≤ (3 : ℝ) * (2 : ℝ) ^ ((D : ℝ) - 2) :=
        GB.Tsum_one_le x (by omega)
      have hnum := gb_rpow_exp_le_one D hD
      calc (Nat.card {p : (Fin 1 → Fin D → ZMod 2) × (Fin 1 → Fin D → ZMod 2) //
              GB.pairCond p.1 p.2 x} : ℝ)
          = (2 : ℝ) ^ (((1 : ℕ) : ℝ) * (D : ℝ)) * GB.Tsum x 1 := hA
        _ ≤ (2 : ℝ) ^ (((1 : ℕ) : ℝ) * (D : ℝ)) * ((3 : ℝ) * (2 : ℝ) ^ ((D : ℝ) - 2)) :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt (GB.two_pow_pos _))
        _ = (3 : ℝ) * (2 : ℝ) ^ (2 * (D : ℝ) - 2) := by
            have he : (((1 : ℕ) : ℝ) * (D : ℝ)) + ((D : ℝ) - 2) = 2 * (D : ℝ) - 2 := by ring
            rw [show (2 : ℝ) ^ (((1 : ℕ) : ℝ) * (D : ℝ)) * (3 * (2 : ℝ) ^ ((D : ℝ) - 2))
                = 3 * ((2 : ℝ) ^ (((1 : ℕ) : ℝ) * (D : ℝ)) * (2 : ℝ) ^ ((D : ℝ) - 2)) from by
                  ring,
              GB.two_pow_add, he]
        _ ≤ (2 : ℝ) ^ (2 * (D : ℝ)) * (2 : ℝ) ^ (-(1 : ℝ) / 4) := hnum
        _ = (2 : ℝ) ^ (2 * 1 * D) * (2 : ℝ) ^ (-(((1 : ℕ) : ℝ)) ^ 2 / 4) := by
            have ha : (2 : ℝ) ^ (2 * 1 * D) = (2 : ℝ) ^ (2 * (D : ℝ)) := by
              rw [← Real.rpow_natCast]
              congr 1
              push_cast
              ring
            have hb : (2 : ℝ) ^ (-(((1 : ℕ) : ℝ)) ^ 2 / 4) = (2 : ℝ) ^ (-(1 : ℝ) / 4) := by
              congr 1
              norm_num
            rw [ha, hb]
  · have hT : GB.Tsum x r ≤ (2 : ℝ) ^ ((r : ℝ) * (D : ℝ) - (r : ℝ) * ((r : ℝ) - 1) / 2) :=
      GB.Tsum_le x r hr2 hr
    calc (Nat.card {p : (Fin r → Fin D → ZMod 2) × (Fin r → Fin D → ZMod 2) //
            GB.pairCond p.1 p.2 x} : ℝ)
        = (2 : ℝ) ^ ((r : ℝ) * (D : ℝ)) * GB.Tsum x r := hA
      _ ≤ (2 : ℝ) ^ ((r : ℝ) * (D : ℝ)) *
            (2 : ℝ) ^ ((r : ℝ) * (D : ℝ) - (r : ℝ) * ((r : ℝ) - 1) / 2) :=
          mul_le_mul_of_nonneg_left hT (le_of_lt (GB.two_pow_pos _))
      _ = (2 : ℝ) ^ (2 * (r : ℝ) * (D : ℝ) - (r : ℝ) * ((r : ℝ) - 1) / 2) := by
          rw [GB.two_pow_add]
          congr 1
          ring
      _ ≤ (2 : ℝ) ^ (2 * (r : ℝ) * (D : ℝ) - (r : ℝ) ^ 2 / 4) := gb_rpow_exp_le D r hr2
      _ = (2 : ℝ) ^ (2 * r * D) * (2 : ℝ) ^ (-(r : ℝ) ^ 2 / 4) := by
          rw [← Real.rpow_natCast (2 : ℝ) (2 * r * D), GB.two_pow_add]
          congr 1
          push_cast
          ring

end Work.LT
