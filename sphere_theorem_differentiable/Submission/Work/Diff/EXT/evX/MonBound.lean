import Mathlib
import Submission.Work.Diff.EXT.evX.MonDefs
import Submission.Work.Diff.EXT.evX.rmSym_boundV
import Submission.Work.Diff.EXT.evX.Partition

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.evX

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! ## The building blocks of the monomial bound

* `MonBound_prod_partition`: if three families `d₁`, `d₂`, `s` of positions of `Fin N` are injective,
  pairwise disjoint and cover `Fin N`, then a product over `Fin N` splits into the three products.
* `sPos_injectiveV`: the four `reactionMap`-slots are pairwise distinct.
* `MonBound_prod_append`: a product over `Fin (a+c)` of `Fin.append u v` splits.
* `MonBound_frame_prod`: the four frame vectors of an orthonormal frame have unit length, so their
  product of square roots is `1`.
* `MonBound_tower_entry`: **the sharp entry bound for the tower** — an entry of the array of
  components of `∇^a Rm` in the frame `e` is bounded by `√(curvNormK g x a)` times the product of
  the norms of the differentiation directions.
* `MonBound_sum4_const`, `MonBound_abs_sum4_le`, `MonBound_abs_mul4_le`: the elementary estimates
  for the four nested frame sums.
* `MonBound_MonoD_boundV`: the monomial bound for arbitrary index maps (the analytic core). -/

/-- A product over `Fin N` splits into the products over three families of positions which are
injective, pairwise disjoint and cover `Fin N`. -/
lemma MonBound_prod_partition {N a b : ℕ}
    (d₁ : Fin a → Fin N) (d₂ : Fin b → Fin N) (s : Fin 4 → Fin N)
    (h₁ : Function.Injective d₁) (h₂ : Function.Injective d₂) (h₃ : Function.Injective s)
    (hd₁₂ : ∀ r r', d₁ r ≠ d₂ r') (hd₁₃ : ∀ r t, d₁ r ≠ s t) (hd₂₃ : ∀ r t, d₂ r ≠ s t)
    (hcov : ∀ u : Fin N, (∃ r, d₁ r = u) ∨ (∃ r, d₂ r = u) ∨ (∃ t, s t = u))
    (B : Fin N → ℝ) :
    (∏ r : Fin a, B (d₁ r)) * (∏ r : Fin b, B (d₂ r)) * (∏ t : Fin 4, B (s t))
      = ∏ u : Fin N, B u := by
  classical
  set A₁ : Finset (Fin N) := Finset.univ.image d₁ with hA₁
  set A₂ : Finset (Fin N) := Finset.univ.image d₂ with hA₂
  set A₃ : Finset (Fin N) := Finset.univ.image s with hA₃
  have hp₁ : (∏ y ∈ A₁, B y) = ∏ r : Fin a, B (d₁ r) := by
    rw [hA₁]
    exact Finset.prod_image (f := B) (g := d₁) (s := Finset.univ) (fun x _ y _ h => h₁ h)
  have hp₂ : (∏ y ∈ A₂, B y) = ∏ r : Fin b, B (d₂ r) := by
    rw [hA₂]
    exact Finset.prod_image (f := B) (g := d₂) (s := Finset.univ) (fun x _ y _ h => h₂ h)
  have hp₃ : (∏ y ∈ A₃, B y) = ∏ t : Fin 4, B (s t) := by
    rw [hA₃]
    exact Finset.prod_image (f := B) (g := s) (s := Finset.univ) (fun x _ y _ h => h₃ h)
  have hdisj₁₂ : Disjoint A₁ A₂ := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    rw [hA₁, Finset.mem_image] at hu
    rw [hA₂, Finset.mem_image] at hu'
    obtain ⟨r, -, hr⟩ := hu
    obtain ⟨r', -, hr'⟩ := hu'
    exact hd₁₂ r r' (by rw [hr, hr'])
  have hdisj₁₃ : Disjoint A₁ A₃ := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    rw [hA₁, Finset.mem_image] at hu
    rw [hA₃, Finset.mem_image] at hu'
    obtain ⟨r, -, hr⟩ := hu
    obtain ⟨t, -, ht⟩ := hu'
    exact hd₁₃ r t (by rw [hr, ht])
  have hdisj₂₃ : Disjoint A₂ A₃ := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    rw [hA₂, Finset.mem_image] at hu
    rw [hA₃, Finset.mem_image] at hu'
    obtain ⟨r, -, hr⟩ := hu
    obtain ⟨t, -, ht⟩ := hu'
    exact hd₂₃ r t (by rw [hr, ht])
  have hdisj₁₂₃ : Disjoint (A₁ ∪ A₂) A₃ := by
    rw [Finset.disjoint_union_left]
    exact ⟨hdisj₁₃, hdisj₂₃⟩
  have hunion : A₁ ∪ A₂ ∪ A₃ = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro u
    rcases hcov u with ⟨r, hr⟩ | ⟨r, hr⟩ | ⟨t, ht⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (by rw [hA₁, Finset.mem_image]; exact ⟨r, Finset.mem_univ _, hr⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (by rw [hA₂, Finset.mem_image]; exact ⟨r, Finset.mem_univ _, hr⟩))
    · exact Finset.mem_union_right _
        (by rw [hA₃, Finset.mem_image]; exact ⟨t, Finset.mem_univ _, ht⟩)
  have hsplit : (∏ u ∈ A₁ ∪ A₂ ∪ A₃, B u)
      = (∏ u ∈ A₁, B u) * (∏ u ∈ A₂, B u) * (∏ u ∈ A₃, B u) := by
    rw [Finset.prod_union hdisj₁₂₃, Finset.prod_union hdisj₁₂]
  rw [← hp₁, ← hp₂, ← hp₃, ← hsplit, hunion]

/-- The positions of the four `reactionMap`-slots of `sPos n` are pairwise distinct. -/
lemma sPos_injectiveV (n : ℕ) : Function.Injective (sPos n) := by
  intro t t' h
  have h' := congrArg Fin.val h
  simp only [sPos] at h'
  exact Fin.ext (by omega)

/-- A product over `Fin (a + c)` of `Fin.append u v` splits into the two products. -/
lemma MonBound_prod_append {X M' : Type*} [CommMonoid M'] {a c : ℕ} (u : Fin a → X)
    (v : Fin c → X) (D : X → M') :
    (∏ s : Fin (a + c), D (Fin.append u v s)) = (∏ r : Fin a, D (u r)) * ∏ t : Fin c, D (v t) := by
  rw [Fin.prod_univ_add (f := fun s => D (Fin.append u v s))]
  congr 1
  · exact Finset.prod_congr rfl (fun i _ => by rw [Fin.append_left])
  · exact Finset.prod_congr rfl (fun i _ => by rw [Fin.append_right])

/-- The product of the square roots of the lengths of the four frame vectors
`e i x, e j x, e k x, e l x` of an orthonormal frame is `1`. -/
lemma MonBound_frame_prod (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (hON : IsONFrame g x (fun i => e i x)) (i j k l : Fin (Module.finrank ℝ E)) :
    (∏ t : Fin 4, Real.sqrt (g.inner x ((![e i x, e j x, e k x, e l x] : Fin 4 → TangentSpace I x) t)
        ((![e i x, e j x, e k x, e l x] : Fin 4 → TangentSpace I x) t))) = 1 := by
  rw [Fin.prod_univ_four]
  have h0 : g.inner x (e i x) (e i x) = 1 := by simpa using hON i i
  have h1 : g.inner x (e j x) (e j x) = 1 := by simpa using hON j j
  have h2 : g.inner x (e k x) (e k x) = 1 := by simpa using hON k k
  have h3 : g.inner x (e l x) (e l x) = 1 := by simpa using hON l l
  simp [h0, h1, h2, h3]

/-- **The sharp entry bound for the tower**: an entry of the array of the components of `∇^a Rm` in
the frame field `e` at `x` is bounded by `√(curvNormK g x a)` times the product of the `g`-norms of
the differentiation directions.  (The four curvature slots are filled by the frame vectors, which
have norm `1` because `e` is orthonormal at `x`.) -/
lemma MonBound_tower_entry (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (a : ℕ) (dirs : Fin a → TField (I := I) (M := M))
    (hdirs : ∀ r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (dirs r))
    (e : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i)) (x : M)
    (hON : IsONFrame g x (fun i => e i x)) (i j k l : Fin (Module.finrank ℝ E)) :
    |TowerArr g a dirs e x i j k l| ≤
      Real.sqrt (curvNormK g x a) * ∏ r : Fin a, Real.sqrt (g.inner x (dirs r x) (dirs r x)) := by
  set u : Fin a → TangentSpace I x := fun r => dirs r x with hu
  set v : Fin 4 → TangentSpace I x := ![e i x, e j x, e k x, e l x] with hv
  have hkey : TowerArr g a dirs e x i j k l = Kpt g x a (Fin.append u v) := by
    rw [TowerArr_eq_KptArr hLC g a dirs hdirs e he x]
    simp only [KptArr, hu, hv]
  rw [hkey]
  refine le_trans (Kpt_norm_bound hLC g x a (Fin.append u v)) ?_
  have hceil : (∏ s : Fin (a + 4), Real.sqrt (g.inner x (Fin.append u v s) (Fin.append u v s)))
      = (∏ r : Fin a, Real.sqrt (g.inner x (u r) (u r)))
        * (∏ t : Fin 4, Real.sqrt (g.inner x (v t) (v t))) :=
    MonBound_prod_append u v (fun m => Real.sqrt (g.inner x m m))
  rw [hceil, hv]
  have hone : (∏ t : Fin 4, Real.sqrt (g.inner x
      ((![e i x, e j x, e k x, e l x] : Fin 4 → TangentSpace I x) t)
      ((![e i x, e j x, e k x, e l x] : Fin 4 → TangentSpace I x) t))) = 1 :=
    MonBound_frame_prod g x e hON i j k l
  rw [hone, mul_one, hu]

/-- A sum of a constant over the four-fold product of `Fin d` is `d^4 * c`. -/
lemma MonBound_sum4_const {d : ℕ} (c : ℝ) :
    (∑ _i : Fin d, ∑ _j : Fin d, ∑ _k : Fin d, ∑ _l : Fin d, c) = (d : ℝ)^4 * c := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The four-fold sum of a term bounded by `C` is bounded by `d^4 * C`. -/
lemma MonBound_abs_sum4_le {d : ℕ} (f : Fin d → Fin d → Fin d → Fin d → ℝ) {C : ℝ}
    (h : ∀ i j k l, |f i j k l| ≤ C) :
    |∑ i, ∑ j, ∑ k, ∑ l, f i j k l| ≤ (d : ℝ)^4 * C := by
  have h1 : |∑ i, ∑ j, ∑ k, ∑ l, f i j k l| ≤ ∑ i, ∑ j, ∑ k, ∑ l, |f i j k l| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum (fun k _ => ?_)
    exact Finset.abs_sum_le_sum_abs _ _
  refine le_trans h1 ?_
  refine le_trans (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
    Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => h i j k l))))) ?_
  rw [MonBound_sum4_const]

/-- A product of four factors, bounded factorwise (with nonnegative bounds). -/
lemma MonBound_abs_mul4_le {a b c d A B C D : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hd : |d| ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (_hD : 0 ≤ D) :
    |a * b * c * d| ≤ A * B * C * D := by
  rw [abs_mul, abs_mul, abs_mul]
  have h1 : |a| * |b| ≤ A * B := mul_le_mul ha hb (abs_nonneg _) hA
  have h2 : |a| * |b| * |c| ≤ A * B * C := mul_le_mul h1 hc (abs_nonneg _) (mul_nonneg hA hB)
  exact mul_le_mul h2 hd (abs_nonneg _) (mul_nonneg (mul_nonneg hA hB) hC)

/-- **The analytic core of the monomial bound.**  For arbitrary index maps `d₁`, `d₂`, `s`, the
monomial `MonoD` is bounded by the product of the two sharp tower bounds (one for each factor of the
reaction) and the product of the norms of the four slot vectors, with the constant `C₀` of the
componentwise bound for `rmSym` and the `(finrank ℝ E)^4` of the four frame sums. -/
lemma MonBound_MonoD_boundV
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hrm : ∀ (X Y : Curv4 (Module.finrank ℝ E)) (Mx My : ℝ), 0 ≤ Mx → 0 ≤ My →
      (∀ i j k l, |X i j k l| ≤ Mx) → (∀ i j k l, |Y i j k l| ≤ My) →
      ∀ i j k l, |rmSym X Y i j k l| ≤ C₀ * Mx * My)
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (N a b : ℕ) (d₁ : Fin a → Fin N) (d₂ : Fin b → Fin N) (s : Fin 4 → Fin N)
    (e : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i))
    (hON : IsONFrame g x (fun i => e i x))
    (F : Fin N → TField (I := I) (M := M))
    (hF : ∀ r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F r)) :
    |MonoD (I := I) (M := M) g N a b d₁ d₂ s e F x| ≤
      C₀ * (Module.finrank ℝ E : ℝ)^4
        * (Real.sqrt (curvNormK g x a)
            * ∏ r : Fin a, Real.sqrt (g.inner x (F (d₁ r) x) (F (d₁ r) x)))
        * (Real.sqrt (curvNormK g x b)
            * ∏ r : Fin b, Real.sqrt (g.inner x (F (d₂ r) x) (F (d₂ r) x)))
        * (∏ t : Fin 4, Real.sqrt (g.inner x (F (s t) x) (F (s t) x))) := by
  classical
  set B : Fin N → ℝ := fun u => Real.sqrt (g.inner x (F u x) (F u x)) with hB
  have hBnn : ∀ u, 0 ≤ B u := fun u => Real.sqrt_nonneg _
  set Mx : ℝ := Real.sqrt (curvNormK g x a) * ∏ r : Fin a, B (d₁ r) with hMx
  set My : ℝ := Real.sqrt (curvNormK g x b) * ∏ r : Fin b, B (d₂ r) with hMy
  set P : ℝ := ∏ t : Fin 4, B (s t) with hP
  have hMxnn : 0 ≤ Mx := by
    rw [hMx]
    exact mul_nonneg (Real.sqrt_nonneg _) (Finset.prod_nonneg fun r _ => hBnn _)
  have hMynn : 0 ≤ My := by
    rw [hMy]
    exact mul_nonneg (Real.sqrt_nonneg _) (Finset.prod_nonneg fun r _ => hBnn _)
  have hpair : ∀ (m : Fin (Module.finrank ℝ E)) (t : Fin 4),
      |g.inner x (e m x) (F (s t) x)| ≤ B (s t) := by
    intro m t
    have h1 : Real.sqrt (g.inner x (e m x) (e m x)) = 1 := by
      rw [hON m m]; simp
    have h := Work.Diff.EXT.inner_pairing_bound g x (e m x) (F (s t) x)
    rw [h1, one_mul] at h
    exact h
  have hterm : ∀ i j k l : Fin (Module.finrank ℝ E),
      |rmSym (TowerArr g a (fun r => F (d₁ r)) e x) (TowerArr g b (fun r => F (d₂ r)) e x)
          i j k l
        * (g.inner x (e i x) (F (s 0) x) * g.inner x (e j x) (F (s 1) x)
          * g.inner x (e k x) (F (s 2) x) * g.inner x (e l x) (F (s 3) x))|
        ≤ C₀ * Mx * My * P := by
    intro i j k l
    have hX : ∀ i j k l, |TowerArr g a (fun r => F (d₁ r)) e x i j k l| ≤ Mx := by
      intro i j k l
      rw [hMx]
      simpa only [hB] using
        MonBound_tower_entry hLC g a (fun r => F (d₁ r)) (fun r => hF (d₁ r)) e he x hON i j k l
    have hY : ∀ i j k l, |TowerArr g b (fun r => F (d₂ r)) e x i j k l| ≤ My := by
      intro i j k l
      rw [hMy]
      simpa only [hB] using
        MonBound_tower_entry hLC g b (fun r => F (d₂ r)) (fun r => hF (d₂ r)) e he x hON i j k l
    have h1 := hrm _ _ Mx My hMxnn hMynn hX hY i j k l
    have h2 := MonBound_abs_mul4_le (hpair i 0) (hpair j 1) (hpair k 2) (hpair l 3)
        (hBnn _) (hBnn _) (hBnn _) (hBnn _)
    have hP4 : P = B (s 0) * B (s 1) * B (s 2) * B (s 3) := by rw [hP, Fin.prod_univ_four]
    rw [abs_mul, hP4]
    exact mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg (mul_nonneg hC₀ hMxnn) hMynn)
  have hsum : |MonoD (I := I) (M := M) g N a b d₁ d₂ s e F x| ≤
      (Module.finrank ℝ E : ℝ)^4 * (C₀ * Mx * My * P) := by
    simp only [MonoD]
    exact MonBound_abs_sum4_le _ hterm
  have hfin : (Module.finrank ℝ E : ℝ)^4 * (C₀ * Mx * My * P)
      = C₀ * (Module.finrank ℝ E : ℝ)^4 * Mx * My * P := by ring
  exact le_trans hsum (le_of_eq hfin)

/-- **The sharp bound for one monomial of the level-`0` reaction ladder.**
For the word `ε : Fin n → Bool` the monomial `Monε g n ε e F x` — the contraction of
`rmSym (∇^a Rm) (∇^b Rm)` (`a = cntT n ε`, `b = cntF n ε`) in the frame field `e` with the tuple `F` — is
bounded by `C * √(curvNormK g x a) * √(curvNormK g x b) * ∏_r √(g.inner x (F r x) (F r x))`, with `C`
depending only on `n` and `finrank ℝ E`.  Only orthonormality of `e` AT the point `x` is needed.

Route: `Work.Diff.EXT.TowerArr_eq_KptArr` (`reactBase`, proved) rewrites the tower array
`TowerArr g a D₁ e x` as the frame components `KptArr g x a (·) (e ·)` of `∇^a Rm` at `x`, so every entry
is bounded by `Work.Diff.EXT.Kpt_norm_bound` (`reactBase`, proved).  The frame vectors have norm `1`
(`IsONFrame`), and the direction entries contribute the product of their norms, so
`|TowerArr g a D₁ e x i j k l| ≤ √(curvNormK g x a) * ∏_{r} ‖D₁ r x‖`.  The contraction with `rmSym` is
bounded entrywise by `Work.Diff.EXT.evX.rmSym_boundV` (proved), and the four pairings by Cauchy–Schwarz
in an orthonormal frame (`|g.inner x (e i x) (F (s t) x)| ≤ ‖F (s t) x‖`, and
`∑_i |g.inner x (e i x) v| ≤ √(finrank ℝ E) * ‖v‖`).  The final reassembly of the products over the
partition of `Fin (4+n)` into the direction positions `map₁`/`map₂` and the slot positions `sPos` uses
`Work.Diff.EXT.evX.Partition`. -/
theorem MonBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (e : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i))
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : M), Submission.Diff.IsONFrame g x (fun i => e i x) →
      ∀ (ε : Fin n → Bool) (F : Fin (4 + n) → Work.Diff.EXT.TField (I := I) (M := M)),
      (∀ u, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F u)) →
      |Work.Diff.EXT.evX.Monε (I := I) (M := M) g n ε e F x|
        ≤ C * Real.sqrt (Work.Diff.EXT.curvNormK g x (Work.Diff.EXT.evX.cntT n ε))
          * Real.sqrt (Work.Diff.EXT.curvNormK g x (Work.Diff.EXT.evX.cntF n ε))
          * Finset.univ.prod (fun r : Fin (4 + n) =>
              Real.sqrt (g.inner x (F r x) (F r x))) := by
  classical
  obtain ⟨C₀, hC₀, hrm⟩ := rmSym_boundV (Module.finrank ℝ E)
  refine ⟨C₀ * (Module.finrank ℝ E : ℝ)^4, mul_nonneg hC₀ (by positivity), ?_⟩
  intro x hON ε F hF
  obtain ⟨hi₁, hi₂, hd₁₂, hd₁₃, hd₂₃, hcov⟩ := Partition (I := I) (M := M) n ε
  have hprod := MonBound_prod_partition (map₁ n ε) (map₂ n ε) (sPos n) hi₁ hi₂
    (sPos_injectiveV n) hd₁₂ hd₁₃ hd₂₃ hcov
    (fun u : Fin (4 + n) => Real.sqrt (g.inner x (F u x) (F u x)))
  have hmain := MonBound_MonoD_boundV (I := I) (M := M) C₀ hC₀ hrm hLC g x (4 + n)
    (cntT n ε) (cntF n ε) (map₁ n ε) (map₂ n ε) (sPos n) e he hON F hF
  simp only [Monε]
  refine le_trans hmain (le_of_eq ?_)
  rw [← hprod]
  ring

end Work.Diff.EXT.evX
