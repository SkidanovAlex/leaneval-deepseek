import Mathlib

/-!
# A smooth path from the identity to any orientation-preserving linear equivalence

For a real vector space `E = EuclideanSpace ℝ (Fin q)` and `A : E ≃L[ℝ] E` with positive
determinant, we build a smooth (`C^∞`) family `γ : ℝ → E ≃L[ℝ] E` with `γ 0 = 1` and `γ 1 = A`,
proving that `GL⁺(q,ℝ)` is smoothly path connected.

The construction is the classical one: Gaussian elimination (Mathlib's
`Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec`) writes the matrix of `A` as
`L * diagonal D * L'` with `L, L'` products of transvections, and `∏ i, D i = det A > 0`.  A path
is then assembled out of three ingredients, each of which is a smooth family of linear equivalences
of `Fin q → ℝ`:

* transvections `1 + c • E_{ij}` (`i ≠ j`) are interpolated by `1 + (t c) • E_{ij}`;
* positive diagonal matrices `diagonal u` (`u i > 0`) are interpolated by `diagonal (exp (t log u))`;
* a signed diagonal matrix `diagonal f` (`f i = ±1`, `∏ f i = 1`, so an even number of `-1`'s) is
  connected to the identity by pairing up the negative coordinates and rotating each pair by `π`.

All the intermediate matrices stay invertible, and smoothness of the resulting map
`(t, x) ↦ γ t x` follows from explicit pointwise formulas.
-/

namespace Work.Drive.PushDisc

open Matrix

variable {q : ℕ}

lemma contDiff_apply_self (i : Fin q) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Fin q → ℝ => y i) :=
  (LinearMap.toContinuousLinearMap (LinearMap.proj i : (Fin q → ℝ) →ₗ[ℝ] ℝ)).contDiff

lemma contDiff_snd_apply (i : Fin q) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin q → ℝ) => p.2 i) :=
  (contDiff_apply_self i).comp contDiff_snd


/-! ## Transvections -/

/-- The transvection `y ↦ y + (c * y j) • e i`, as a linear endomorphism of `Fin q → ℝ`. -/
noncomputable def tvLM (i j : Fin q) (c : ℝ) : (Fin q → ℝ) →ₗ[ℝ] (Fin q → ℝ) :=
  Matrix.toLin' (Matrix.single i j c)

@[simp]
lemma tvLM_apply (i j : Fin q) (c : ℝ) (y : Fin q → ℝ) (k : Fin q) :
    tvLM i j c y k = if k = i then c * y j else 0 := by
  rw [tvLM, Matrix.toLin'_apply, Matrix.single_mulVec]
  rcases eq_or_ne k i with rfl | hk
  · rw [Function.update_self, if_pos rfl]
  · rw [Function.update_of_ne hk, Pi.zero_apply, if_neg hk]

lemma tvLM_comp_self (i j : Fin q) (hij : i ≠ j) (c d : ℝ) :
    (tvLM i j c).comp (tvLM i j d) = 0 := by
  apply LinearMap.ext; intro y
  rw [LinearMap.comp_apply, LinearMap.zero_apply]
  funext k
  simp only [tvLM_apply]
  by_cases h : k = i <;> simp [h, Ne.symm hij]

lemma tvLM_add (i j : Fin q) (c d : ℝ) : tvLM i j (c + d) = tvLM i j c + tvLM i j d := by
  apply LinearMap.ext; intro y
  rw [LinearMap.add_apply]
  funext k
  simp only [tvLM_apply, Pi.add_apply]
  by_cases h : k = i <;> simp [h, add_mul]

/-- The transvection `1 + c • E_{ij}` as a linear equivalence. -/
noncomputable def tvEquiv (i j : Fin q) (hij : i ≠ j) (c : ℝ) :
    (Fin q → ℝ) ≃ₗ[ℝ] (Fin q → ℝ) :=
  LinearEquiv.ofLinearMap (LinearMap.id + tvLM i j c) (LinearMap.id - tvLM i j c)
    (by
      apply LinearMap.ext; intro y
      have h : tvLM i j c (tvLM i j c y) = 0 := by
        rw [← LinearMap.comp_apply, tvLM_comp_self i j hij c c, LinearMap.zero_apply]
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
        map_sub, h]
      abel)
    (by
      apply LinearMap.ext; intro y
      have h : tvLM i j c (tvLM i j c y) = 0 := by
        rw [← LinearMap.comp_apply, tvLM_comp_self i j hij c c, LinearMap.zero_apply]
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply,
        map_add, h]
      abel)

lemma tvEquiv_apply (i j : Fin q) (hij : i ≠ j) (c : ℝ) (y : Fin q → ℝ) :
    tvEquiv i j hij c y = fun k => y k + if k = i then c * y j else 0 := by
  rw [tvEquiv, LinearEquiv.coe_ofLinearMap]
  funext k
  rw [LinearMap.add_apply, LinearMap.id_apply, Pi.add_apply, tvLM_apply]

lemma tvEquiv_zero (i j : Fin q) (hij : i ≠ j) : tvEquiv i j hij 0 = 1 := by
  apply LinearEquiv.ext
  intro y
  rw [tvEquiv_apply, LinearEquiv.coe_one, id_eq]
  funext k
  simp

lemma tvEquiv_eq_toLin' (i j : Fin q) (hij : i ≠ j) (c : ℝ) (z : Fin q → ℝ) :
    tvEquiv i j hij c z = Matrix.toLin' (Matrix.transvection i j c) z := by
  rw [tvEquiv_apply, Matrix.transvection, Matrix.toLin'_apply, Matrix.add_mulVec,
    Matrix.one_mulVec, Matrix.single_mulVec]
  funext k
  rw [Pi.add_apply]
  by_cases h : k = i
  · subst h; simp [Function.update_self]
  · rw [Function.update_of_ne h]; simp [h]

/-! ## Diagonal scalings -/

/-- The diagonal scaling `y ↦ fun i => t i * y i`. -/
noncomputable def diagLM (t : Fin q → ℝ) : (Fin q → ℝ) →ₗ[ℝ] (Fin q → ℝ) :=
  LinearMap.pi (fun i => t i • LinearMap.proj i)

lemma diagLM_apply (t : Fin q → ℝ) (y : Fin q → ℝ) (i : Fin q) :
    diagLM t y i = t i * y i := by
  rw [diagLM, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

/-- The diagonal linear equivalence `diagonal t` for a nowhere vanishing `t`. -/
noncomputable def diagEquiv (t : Fin q → ℝ) (ht : ∀ i, t i ≠ 0) :
    (Fin q → ℝ) ≃ₗ[ℝ] (Fin q → ℝ) :=
  LinearEquiv.ofLinearMap (diagLM t) (diagLM (fun i => (t i)⁻¹))
    (by
      apply LinearMap.ext; intro y
      rw [LinearMap.comp_apply, LinearMap.id_apply]
      funext i
      rw [diagLM_apply, diagLM_apply, ← mul_assoc, mul_inv_cancel₀ (ht i), one_mul])
    (by
      apply LinearMap.ext; intro y
      rw [LinearMap.comp_apply, LinearMap.id_apply]
      funext i
      rw [diagLM_apply, diagLM_apply, ← mul_assoc, inv_mul_cancel₀ (ht i), one_mul])

lemma diagEquiv_apply (t : Fin q → ℝ) (ht : ∀ i, t i ≠ 0) (y : Fin q → ℝ) (i : Fin q) :
    diagEquiv t ht y i = t i * y i := by
  rw [diagEquiv, LinearEquiv.coe_ofLinearMap, diagLM_apply]

lemma diagEquiv_apply_of_pos (u : Fin q → ℝ) (hu : ∀ i, 0 < u i) (y : Fin q → ℝ) (i : Fin q) :
    diagEquiv u (fun i => (hu i).ne') y i = u i * y i :=
  diagEquiv_apply u _ y i

/-! ## The class of "smoothly path connected to the identity" linear equivalences -/

/-- `GoodLM L` means that `L` can be joined to the identity by a smooth path of linear
equivalences (smooth jointly in the path parameter and the vector). -/
def GoodLM (L : (Fin q → ℝ) ≃ₗ[ℝ] (Fin q → ℝ)) : Prop :=
  ∃ P : ℝ → (Fin q → ℝ) ≃ₗ[ℝ] (Fin q → ℝ), P 0 = 1 ∧ P 1 = L ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin q → ℝ) => P p.1 p.2)

lemma goodLM_refl : GoodLM (1 : (Fin q → ℝ) ≃ₗ[ℝ] (Fin q → ℝ)) :=
  ⟨fun _ => 1, rfl, rfl, by simpa [LinearEquiv.coe_one] using contDiff_snd⟩

lemma goodLM_trans {L₁ L₂ : (Fin q → ℝ) ≃ₗ[ℝ] (Fin q → ℝ)} (h₁ : GoodLM L₁)
    (h₂ : GoodLM L₂) : GoodLM (L₁.trans L₂) := by
  obtain ⟨P₁, hP₁₀, hP₁₁, hP₁⟩ := h₁
  obtain ⟨P₂, hP₂₀, hP₂₁, hP₂⟩ := h₂
  refine ⟨fun s => (P₁ s).trans (P₂ s), ?_, ?_, ?_⟩
  · show (P₁ 0).trans (P₂ 0) = 1
    rw [hP₁₀, hP₂₀, LinearEquiv.one_eq_refl, LinearEquiv.refl_trans]
  · show (P₁ 1).trans (P₂ 1) = L₁.trans L₂
    rw [hP₁₁, hP₂₁]
  · have h : (fun p : ℝ × (Fin q → ℝ) => ((P₁ p.1).trans (P₂ p.1)) p.2)
        = fun p : ℝ × (Fin q → ℝ) => P₂ p.1 (P₁ p.1 p.2) := by
      funext p; rw [LinearEquiv.trans_apply]
    rw [h]
    exact hP₂.comp (contDiff_fst.prodMk hP₁)

/-- A transvection is smoothly connected to the identity. -/
lemma goodLM_tvEquiv (i j : Fin q) (hij : i ≠ j) (c : ℝ) : GoodLM (tvEquiv i j hij c) := by
  refine ⟨fun s => tvEquiv i j hij (s * c), ?_, ?_, ?_⟩
  · show tvEquiv i j hij (0 * c) = 1
    rw [zero_mul]; exact tvEquiv_zero i j hij
  · show tvEquiv i j hij (1 * c) = tvEquiv i j hij c
    rw [one_mul]
  · have h : (fun p : ℝ × (Fin q → ℝ) => tvEquiv i j hij (p.1 * c) p.2)
        = fun p : ℝ × (Fin q → ℝ) => fun k => p.2 k + if k = i then (p.1 * c) * p.2 j else 0 := by
      funext p; funext k
      rw [tvEquiv_apply]
    rw [h]
    rw [contDiff_pi]
    intro k
    refine ContDiff.add ?_ ?_
    · exact contDiff_snd_apply k
    · by_cases hk : k = i
      · simp only [if_pos hk]
        exact (contDiff_fst.mul contDiff_const).mul (contDiff_snd_apply j)
      · simp only [if_neg hk]
        exact contDiff_const

/-- A diagonal matrix with positive entries is smoothly connected to the identity. -/
lemma goodLM_diagEquiv_pos (u : Fin q → ℝ) (hu : ∀ i, 0 < u i) :
    ∃ L : (Fin q → ℝ) ≃ₗ[ℝ] (Fin q → ℝ), (∀ y i, L y i = u i * y i) ∧ GoodLM L := by
  refine ⟨diagEquiv u (fun i => (hu i).ne'), ?_, ?_⟩
  · intro y i
    exact diagEquiv_apply u (fun i => (hu i).ne') y i
  refine ⟨fun s => diagEquiv (fun i => Real.exp (s * Real.log (u i))) (fun i => Real.exp_ne_zero _),
    ?_, ?_, ?_⟩
  · apply LinearEquiv.ext; intro y; funext i
    simp only [diagEquiv_apply, LinearEquiv.coe_one, id_eq]
    simp
  · apply LinearEquiv.ext; intro y; funext i
    simp only [diagEquiv_apply, one_mul, Real.exp_log (hu i)]
  · have h : (fun p : ℝ × (Fin q → ℝ) =>
          diagEquiv (fun i => Real.exp (p.1 * Real.log (u i))) (fun i => Real.exp_ne_zero _) p.2)
        = fun p : ℝ × (Fin q → ℝ) => fun i => Real.exp (p.1 * Real.log (u i)) * p.2 i := by
      funext p; funext i; exact diagEquiv_apply _ _ _ _
    rw [h]
    rw [contDiff_pi]
    intro i
    exact (Real.contDiff_exp.comp (contDiff_fst.mul contDiff_const)).mul
      (contDiff_snd_apply i)

/-! ## Rotation in a pair of coordinates -/

/-- Rotation by the angle `π * s` in the coordinate plane spanned by `e a` and `e b`. -/
noncomputable def rotPairLM (a b : Fin q) (s : ℝ) : (Fin q → ℝ) →ₗ[ℝ] (Fin q → ℝ) :=
  LinearMap.pi (fun k =>
    if k = a then (Real.cos (Real.pi * s)) • LinearMap.proj a + (Real.sin (Real.pi * s)) • LinearMap.proj b
    else if k = b then (-(Real.sin (Real.pi * s))) • LinearMap.proj a + (Real.cos (Real.pi * s)) • LinearMap.proj b
    else LinearMap.proj k)

lemma rotPairLM_apply (a b : Fin q) (hab : a ≠ b) (s : ℝ) (y : Fin q → ℝ) (k : Fin q) :
    rotPairLM a b s y k = if k = a then Real.cos (Real.pi * s) * y a + Real.sin (Real.pi * s) * y b
      else if k = b then -(Real.sin (Real.pi * s)) * y a + Real.cos (Real.pi * s) * y b
      else y k := by
  rw [rotPairLM, LinearMap.pi_apply]
  by_cases h : k = a
  · subst h
    simp only [if_true, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  · rw [if_neg h]
    by_cases h2 : k = b
    · subst h2
      simp only [if_neg (Ne.symm hab), if_true, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.proj_apply, smul_eq_mul]
    · rw [if_neg h2, LinearMap.proj_apply, if_neg h, if_neg h2]

lemma rotPairLM_apply_a (a b : Fin q) (hab : a ≠ b) (s : ℝ) (y : Fin q → ℝ) :
    rotPairLM a b s y a = Real.cos (Real.pi * s) * y a + Real.sin (Real.pi * s) * y b := by
  rw [rotPairLM_apply a b hab s y a, if_pos rfl]

lemma rotPairLM_apply_b (a b : Fin q) (hab : a ≠ b) (s : ℝ) (y : Fin q → ℝ) :
    rotPairLM a b s y b = -(Real.sin (Real.pi * s)) * y a + Real.cos (Real.pi * s) * y b := by
  rw [rotPairLM_apply a b hab s y b, if_neg (Ne.symm hab), if_pos rfl]

lemma rotPairLM_apply_of_ne (a b : Fin q) (hab : a ≠ b) (s : ℝ) (y : Fin q → ℝ) {k : Fin q}
    (h : k ≠ a) (h2 : k ≠ b) : rotPairLM a b s y k = y k := by
  rw [rotPairLM_apply a b hab s y k, if_neg h, if_neg h2]

lemma rotPairLM_comp_neg_apply (a b : Fin q) (hab : a ≠ b) (s : ℝ) (y : Fin q → ℝ) (k : Fin q) :
    rotPairLM a b s (rotPairLM a b (-s) y) k = y k := by
  by_cases h : k = a
  · rw [h]
    rw [rotPairLM_apply_a a b hab s (rotPairLM a b (-s) y), rotPairLM_apply_a a b hab (-s) y,
      rotPairLM_apply_b a b hab (-s) y]
    simp only [mul_neg, Real.cos_neg, Real.sin_neg]
    ring_nf
    rw [Real.sin_sq, Real.cos_sq]
    ring
  · by_cases h2 : k = b
    · rw [h2]
      rw [rotPairLM_apply_b a b hab s (rotPairLM a b (-s) y), rotPairLM_apply_a a b hab (-s) y,
        rotPairLM_apply_b a b hab (-s) y]
      simp only [mul_neg, Real.cos_neg, Real.sin_neg]
      ring_nf
      rw [Real.sin_sq, Real.cos_sq]
      ring
    · rw [rotPairLM_apply_of_ne a b hab s (rotPairLM a b (-s) y) h h2,
        rotPairLM_apply_of_ne a b hab (-s) y h h2]

lemma rotPairLM_comp_neg (a b : Fin q) (hab : a ≠ b) (s : ℝ) :
    (rotPairLM a b s).comp (rotPairLM a b (-s)) = LinearMap.id := by
  apply LinearMap.ext; intro y
  rw [LinearMap.comp_apply, LinearMap.id_apply]
  funext k
  exact rotPairLM_comp_neg_apply a b hab s y k

lemma rotPairLM_neg_comp (a b : Fin q) (hab : a ≠ b) (s : ℝ) :
    (rotPairLM a b (-s)).comp (rotPairLM a b s) = LinearMap.id := by
  have h := rotPairLM_comp_neg a b hab (-s)
  simpa using h

/-- The rotation by `π * s` in the plane of `a, b`. -/
noncomputable def rotPairEquiv (a b : Fin q) (hab : a ≠ b) (s : ℝ) :
    (Fin q → ℝ) ≃ₗ[ℝ] (Fin q → ℝ) :=
  LinearEquiv.ofLinearMap (rotPairLM a b s) (rotPairLM a b (-s))
    (rotPairLM_comp_neg a b hab s) (rotPairLM_neg_comp a b hab s)

lemma rotPairEquiv_apply (a b : Fin q) (hab : a ≠ b) (s : ℝ) (y : Fin q → ℝ) (k : Fin q) :
    rotPairEquiv a b hab s y k =
      if k = a then Real.cos (Real.pi * s) * y a + Real.sin (Real.pi * s) * y b
      else if k = b then -(Real.sin (Real.pi * s)) * y a + Real.cos (Real.pi * s) * y b
      else y k :=
  rotPairLM_apply a b hab s y k

lemma rotPairEquiv_zero (a b : Fin q) (hab : a ≠ b) : rotPairEquiv a b hab 0 = 1 := by
  apply LinearEquiv.ext; intro y
  funext k
  rw [rotPairEquiv_apply, LinearEquiv.coe_one, id_eq]
  by_cases h : k = a
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]
    by_cases h2 : k = b
    · rw [if_pos h2]; simp [h2]
    · rw [if_neg h2]

lemma rotPairEquiv_one_apply (a b : Fin q) (hab : a ≠ b) (y : Fin q → ℝ) (k : Fin q) :
    rotPairEquiv a b hab 1 y k = if k = a then -y a else if k = b then -y b else y k := by
  rw [rotPairEquiv_apply, mul_one, Real.cos_pi, Real.sin_pi]
  by_cases hk : k = a
  · simp only [if_pos hk]
    ring
  · simp only [if_neg hk]
    by_cases hk2 : k = b
    · simp only [if_pos hk2]
      ring
    · simp only [if_neg hk2]

/-- A rotation by `π` in a coordinate pair is smoothly connected to the identity. -/
lemma goodLM_rotPairEquiv (a b : Fin q) (hab : a ≠ b) : GoodLM (rotPairEquiv a b hab 1) := by
  refine ⟨fun s => rotPairEquiv a b hab s, rotPairEquiv_zero a b hab, rfl, ?_⟩
  have h : (fun p : ℝ × (Fin q → ℝ) => rotPairEquiv a b hab p.1 p.2)
      = fun p : ℝ × (Fin q → ℝ) => fun k =>
          if k = a then Real.cos (Real.pi * p.1) * p.2 a + Real.sin (Real.pi * p.1) * p.2 b
          else if k = b then -(Real.sin (Real.pi * p.1)) * p.2 a + Real.cos (Real.pi * p.1) * p.2 b
          else p.2 k := by
    funext p; funext k
    rw [rotPairEquiv_apply]
  rw [h]
  rw [contDiff_pi]
  intro k
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (Fin q → ℝ) => Real.cos (Real.pi * p.1)) :=
    Real.contDiff_cos.comp (contDiff_const.mul contDiff_fst)
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (Fin q → ℝ) => Real.sin (Real.pi * p.1)) :=
    Real.contDiff_sin.comp (contDiff_const.mul contDiff_fst)
  by_cases hk : k = a
  · simp only [if_pos hk]
    exact (hc.mul (contDiff_snd_apply a)).add (hs.mul (contDiff_snd_apply b))
  · simp only [if_neg hk]
    by_cases hk2 : k = b
    · simp only [if_pos hk2]
      exact ((hs.neg.mul (contDiff_snd_apply a))).add (hc.mul (contDiff_snd_apply b))
    · simp only [if_neg hk2]
      exact contDiff_snd_apply k

/-! ## Signed diagonal matrices -/

/-- A diagonal matrix with entries `±1` and an even number of `-1`'s is smoothly connected to the
identity: pair the negative coordinates and rotate each pair. -/
lemma exists_goodLM_diag_signed (S : Finset (Fin q)) :
    ∀ (f : Fin q → ℝ), (∀ i ∈ S, f i = -1) → (∀ i ∉ S, f i = 1) → Even S.card →
    ∃ L : (Fin q → ℝ) ≃ₗ[ℝ] (Fin q → ℝ), (∀ y i, L y i = f i * y i) ∧ GoodLM L := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro f hmem hnot heven
    by_cases hS : S = ∅
    · subst hS
      refine ⟨1, ?_, goodLM_refl⟩
      intro y i
      rw [LinearEquiv.coe_one, id_eq, hnot i (by simp), one_mul]
    · obtain ⟨t, ht⟩ := heven
      have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
      have h1 : 1 < S.card := by omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h1
      set S'' : Finset (Fin q) := (S.erase a).erase b with hS''
      have haS'' : a ∉ S'' := by simp [hS'']
      have hsub : S'' ⊂ S := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨?_, ?_⟩
        · intro x hx
          simp only [hS'', Finset.mem_erase] at hx
          exact hx.2.2
        · intro hEq
          exact haS'' (hEq ▸ ha)
      set f'' : Fin q → ℝ := fun i => if i = a then 1 else if i = b then 1 else f i with hf''
      have hf''_a : f'' a = 1 := by simp [hf'']
      have hf''_b : f'' b = 1 := by simp [hf'', hab]
      have hf''_ne : ∀ i, i ≠ a → i ≠ b → f'' i = f i := by
        intro i hia hib; simp [hf'', hia, hib]
      have hmem'' : ∀ i ∈ S'', f'' i = -1 := by
        intro i hi
        simp only [hS'', Finset.mem_erase] at hi
        rw [hf''_ne i hi.2.1 hi.1]
        exact hmem i hi.2.2
      have hnot'' : ∀ i ∉ S'', f'' i = 1 := by
        intro i hi
        by_cases hia : i = a
        · rw [hia, hf''_a]
        · by_cases hib : i = b
          · rw [hib, hf''_b]
          · rw [hf''_ne i hia hib]
            exact hnot i (by
              intro hiS
              exact hi (by
                simp only [hS'', Finset.mem_erase]
                exact ⟨hib, hia, hiS⟩))
      have heven'' : Even S''.card := by
        have hcard : S''.card = S.card - 2 := by
          rw [hS'']
          have hb' : b ∈ S.erase a := by simp [hb, hab.symm]
          rw [Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha]
          omega
        rw [hcard]
        exact ⟨t - 1, by omega⟩
      obtain ⟨L', hL', hgood'⟩ := ih S'' hsub f'' hmem'' hnot'' heven''
      refine ⟨(rotPairEquiv a b hab 1).trans L', ?_,
        goodLM_trans (goodLM_rotPairEquiv a b hab) hgood'⟩
      intro y i
      rw [LinearEquiv.trans_apply, hL', rotPairEquiv_one_apply]
      by_cases hia : i = a
      · rw [hia, hf''_a, hmem a ha]
        norm_num
      · rw [if_neg hia]
        by_cases hib : i = b
        · rw [hib, hf''_b, hmem b hb]
          norm_num [Ne.symm hab]
        · rw [hf''_ne i hia hib, if_neg hib]

/-! ## Products of transvections -/

/-- The linear equivalence associated with a list of transvections: its matrix is the product of
the transvection matrices, in the same order. -/
noncomputable def tvListEquiv : List (Matrix.TransvectionStruct (Fin q) ℝ) →
    (Fin q → ℝ) ≃ₗ[ℝ] (Fin q → ℝ)
  | [] => 1
  | t :: rest => (tvListEquiv rest).trans (tvEquiv t.i t.j t.hij t.c)

lemma tvListEquiv_apply (Ls : List (Matrix.TransvectionStruct (Fin q) ℝ)) (y : Fin q → ℝ) :
    tvListEquiv Ls y = Matrix.toLin' ((Ls.map (Matrix.TransvectionStruct.toMatrix)).prod) y := by
  induction Ls with
  | nil => simp [tvListEquiv]
  | cons t rest ih =>
    rw [tvListEquiv, LinearEquiv.trans_apply, ih, List.map_cons, List.prod_cons, Matrix.toLin'_mul,
      LinearMap.comp_apply]
    rw [show t.toMatrix = Matrix.transvection t.i t.j t.c from rfl]
    rw [← tvEquiv_eq_toLin']

lemma goodLM_tvListEquiv (Ls : List (Matrix.TransvectionStruct (Fin q) ℝ)) :
    GoodLM (tvListEquiv Ls) := by
  induction Ls with
  | nil => simpa [tvListEquiv] using goodLM_refl
  | cons t rest ih =>
    rw [tvListEquiv]
    exact goodLM_trans ih (goodLM_tvEquiv t.i t.j t.hij t.c)

/-! ## The path in `GL⁺` -/

lemma prod_pm_eq_one_or_neg_one (f : Fin q → ℝ) (hf : ∀ i, f i = 1 ∨ f i = -1) :
    (∏ i, f i) = 1 ∨ (∏ i, f i) = -1 := by
  have h : ∀ s : Finset (Fin q), (∏ i ∈ s, f i) = 1 ∨ (∏ i ∈ s, f i) = -1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact Or.inl (by simp)
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      rcases ih with ih | ih <;> rcases hf a with h | h <;> rw [h, ih] <;> norm_num
  simpa using h Finset.univ

lemma even_card_filter_neg (f : Fin q → ℝ) (hf : ∀ i, f i = 1 ∨ f i = -1)
    (hprod : (∏ i, f i) = 1) :
    Even (Finset.univ.filter (fun i => f i = -1)).card := by
  have hsplit := Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Fin q))
    (fun i => f i = -1) f
  have hone : (∏ i ∈ Finset.univ.filter (fun i => ¬ f i = -1), f i) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    have hni : ¬ (f i = -1) := (Finset.mem_filter.mp hi).2
    rcases hf i with h | h
    · exact h
    · exact absurd h hni
  have hneg : (∏ i ∈ Finset.univ.filter (fun i => f i = -1), f i) =
      (-1 : ℝ) ^ (Finset.univ.filter (fun i => f i = -1)).card :=
    Finset.prod_eq_pow_card (fun i hi => (Finset.mem_filter.mp hi).2)
  rw [hneg, hone, mul_one, hprod] at hsplit
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)).mp hsplit

theorem exists_contDiff_path_to_one {q : ℕ}
    (A : EuclideanSpace ℝ (Fin q) ≃L[ℝ] EuclideanSpace ℝ (Fin q))
    (hA : 0 < LinearMap.det (A : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] EuclideanSpace ℝ (Fin q))) :
    ∃ γ : ℝ → EuclideanSpace ℝ (Fin q) ≃L[ℝ] EuclideanSpace ℝ (Fin q),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × EuclideanSpace ℝ (Fin q) => γ p.1 p.2) ∧
      γ 0 = 1 ∧ γ 1 = A := by
  classical
  let e := EuclideanSpace.equiv (Fin q) ℝ
  -- the conjugated linear equivalence on `Fin q → ℝ`
  let Bc : (Fin q → ℝ) ≃L[ℝ] (Fin q → ℝ) := e.symm.trans (A.trans e)
  let B : (Fin q → ℝ) ≃ₗ[ℝ] (Fin q → ℝ) := Bc.toLinearEquiv
  have hBeq : B.toLinearMap =
      ↑(e.toLinearEquiv) ∘ₗ (A : EuclideanSpace ℝ (Fin q) →ₗ[ℝ] EuclideanSpace ℝ (Fin q)) ∘ₗ
        ↑(e.toLinearEquiv).symm := by
    apply LinearMap.ext; intro y
    simp [B, Bc, ContinuousLinearEquiv.trans_apply, LinearMap.comp_apply]
  have hBdet : 0 < LinearMap.det B.toLinearMap := by
    rw [hBeq, LinearMap.det_conj]
    exact hA
  let M : Matrix (Fin q) (Fin q) ℝ := LinearMap.toMatrix' B.toLinearMap
  have hMdet : 0 < M.det := by
    show 0 < (LinearMap.toMatrix' B.toLinearMap).det
    rw [LinearMap.det_toMatrix']
    exact hBdet
  obtain ⟨L, L', D, hdec⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  have hDdet : (∏ i : Fin q, D i) = M.det := by
    have h : M.det = (Matrix.diagonal D).det := by
      rw [hdec, Matrix.det_mul, Matrix.det_mul, Matrix.TransvectionStruct.det_toMatrix_prod,
        Matrix.TransvectionStruct.det_toMatrix_prod, one_mul, mul_one]
    rw [h, Matrix.det_diagonal]
  have hDpos : 0 < ∏ i : Fin q, D i := by rw [hDdet]; exact hMdet
  have hDne : ∀ i : Fin q, D i ≠ 0 := fun i =>
    (Finset.prod_ne_zero_iff.mp (ne_of_gt hDpos)) i (Finset.mem_univ i)
  -- the sign of `D` and the positive modulus
  let f : Fin q → ℝ := fun i => if D i < 0 then -1 else 1
  have hfval : ∀ i, f i = 1 ∨ f i = -1 := by
    intro i; by_cases h : D i < 0
    · exact Or.inr (by simp [f, h])
    · exact Or.inl (by simp [f, h])
  have hfabs : ∀ i, f i * |D i| = D i := by
    intro i; by_cases h : D i < 0
    · have hle : D i ≤ 0 := le_of_lt h
      simp only [f, if_pos h, abs_of_neg h]
      ring
    · have hpos : 0 < D i := lt_of_le_of_ne (not_lt.mp h) (Ne.symm (hDne i))
      simp only [f, if_neg h, abs_of_pos hpos, one_mul]
  have hfprod_abs : (∏ i, f i) * (∏ i, |D i|) = ∏ i, D i := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => hfabs i)
  have habs_pos : 0 < ∏ i, |D i| := Finset.prod_pos (fun i _ => abs_pos.mpr (hDne i))
  have hfprod_eq : (∏ i, f i) = 1 := by
    have hpos : 0 < ∏ i, f i := by
      have h2 : 0 < (∏ i, f i) * (∏ i, |D i|) := by rw [hfprod_abs]; exact hDpos
      exact pos_of_mul_pos_left h2 (le_of_lt habs_pos)
    rcases prod_pm_eq_one_or_neg_one f hfval with h | h
    · exact h
    · rw [h] at hpos; norm_num at hpos
  obtain ⟨L_sign, hL_sign, hgood_sign⟩ :=
    exists_goodLM_diag_signed (Finset.univ.filter (fun i => f i = -1)) f
      (fun i hi => (Finset.mem_filter.mp hi).2)
      (fun i hi => by
        rcases hfval i with h | h
        · exact h
        · exact absurd h (by
            intro hmem
            exact hi (by simp only [Finset.mem_filter]; exact ⟨Finset.mem_univ i, hmem⟩)))
      (even_card_filter_neg f hfval hfprod_eq)
  obtain ⟨L_pos, hL_pos, hgood_pos⟩ := goodLM_diagEquiv_pos (fun i => |D i|)
    (fun i => abs_pos.mpr (hDne i))
  have hLdiag : ∀ z : Fin q → ℝ,
      (L_pos.trans L_sign) z = Matrix.toLin' (Matrix.diagonal D) z := by
    intro z
    funext i
    rw [LinearEquiv.trans_apply, hL_sign, hL_pos, Matrix.toLin'_apply,
      Matrix.mulVec_diagonal, ← mul_assoc, hfabs i]
  have hgood_diag : GoodLM (L_pos.trans L_sign) := goodLM_trans hgood_pos hgood_sign
  -- the transvection parts
  have hgood_Pl : GoodLM (tvListEquiv L) := goodLM_tvListEquiv L
  have hgood_Pl' : GoodLM (tvListEquiv L') := goodLM_tvListEquiv L'
  set L_M : (Fin q → ℝ) ≃ₗ[ℝ] (Fin q → ℝ) :=
    (tvListEquiv L').trans ((L_pos.trans L_sign).trans (tvListEquiv L)) with hL_Mdef
  have hgood_M : GoodLM L_M :=
    goodLM_trans hgood_Pl' (goodLM_trans hgood_diag hgood_Pl)
  have hLM : ∀ y : Fin q → ℝ, L_M y = Matrix.toLin' M y := by
    intro y
    rw [hL_Mdef, LinearEquiv.trans_apply, LinearEquiv.trans_apply, tvListEquiv_apply L',
      hLdiag, tvListEquiv_apply L, hdec, Matrix.toLin'_mul, Matrix.toLin'_mul,
      LinearMap.comp_apply, LinearMap.comp_apply]
  obtain ⟨P, hP0, hP1, hPsmooth⟩ := hgood_M
  set γ : ℝ → EuclideanSpace ℝ (Fin q) ≃L[ℝ] EuclideanSpace ℝ (Fin q) :=
    fun s => e.trans (((P s).toContinuousLinearEquiv).trans e.symm) with hγdef
  refine ⟨γ, ?_, ?_, ?_⟩
  · have hfun : (fun p : ℝ × EuclideanSpace ℝ (Fin q) => γ p.1 p.2)
        = fun p : ℝ × EuclideanSpace ℝ (Fin q) => e.symm (P p.1 (e p.2)) := by
      funext p
      simp only [hγdef, ContinuousLinearEquiv.trans_apply]
      rfl
    rw [hfun]
    exact (e.symm.contDiff).comp (hPsmooth.comp (contDiff_fst.prodMk (e.contDiff.comp contDiff_snd)))
  · have h : γ 0 = 1 := by
      refine ContinuousLinearEquiv.ext (funext fun x => ?_)
      simp only [hγdef, ContinuousLinearEquiv.trans_apply, hP0,
        LinearEquiv.coe_toContinuousLinearEquiv, LinearEquiv.coe_one, id_eq,
        ContinuousLinearEquiv.symm_apply_apply]
      rfl
    exact h
  · have h : γ 1 = A := by
      refine ContinuousLinearEquiv.ext (funext fun x => ?_)
      have h1 : L_M (e x) = Bc (e x) := by
        rw [hLM, show M = LinearMap.toMatrix' B.toLinearMap from rfl, Matrix.toLin'_toMatrix']
        rfl
      have h2 : e.symm (Bc (e x)) = A x := by
        simp only [Bc, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.symm_apply_apply]
      calc γ 1 x = e.symm (P 1 (e x)) := by
            simp only [hγdef, ContinuousLinearEquiv.trans_apply]
            rfl
        _ = e.symm (L_M (e x)) := by rw [hP1]
        _ = e.symm (Bc (e x)) := by rw [h1]
        _ = A x := h2
    exact h

end Work.Drive.PushDisc
