import Mathlib
import Submission.Commons.Combinatorics.Ramsey.dkt_core_insens

namespace Commons.Combinatorics.Ramsey

/-- The correlation lemma of the Dodos–Kanellopoulos–Tyros density increment, in the form needed by
the density-increment step: the density hypothesis on `A` is only `(δ - 2η) · (k+1)^m ≤ |A|` and
the dichotomy is stated as a plain disjunction of the two alternatives.  Both alternatives are
instances of the insensitive-set construction of `dkt_core_insens`.

The second alternative (many combinatorial lines) is isolated as `dkt_insens_correlation_lines`,
since it is the only place where the weak density hypothesis `(δ - 2η) · (k+1)^m ≤ |A|` (rather
than `δ · (k+1)^m ≤ |A|`) is genuinely required. -/
theorem dkt_insens_correlation_lines (k : ℕ) (hk : 2 ≤ k) (δ θ η γ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hη : η = δ * θ / 48) (hγ : γ = δ * η^2 / k)
    (m : ℕ) (hm1 : 1 ≤ m) (hm : ((k : ℝ) ^ m) ≤ η * (((k+1 : ℕ) : ℝ) ^ m))
    (A : Finset (Fin m → Fin (k+1)))
    (hA : (δ - 2*η) * (((k+1 : ℕ) : ℝ)) ^ m ≤ (A.card : ℝ))
    (hno : ¬ ∃ l : _root_.Combinatorics.Line (Fin (k+1)) (Fin m), ∀ v : Fin (k+1), l v ∈ A)
    (hlines : (θ/2) * ((((k+1 : ℕ) : ℝ) ^ m) - ((k : ℝ) ^ m)) ≤
         (((Commons.Combinatorics.Ramsey.varWord k m).filter
           (fun g => ∀ v : Fin k, Commons.Combinatorics.Ramsey.linePt g v ∈ A)).card : ℝ)) :
    ∃ D : Finset (Fin m → Fin (k+1)),
      (∃ Ds : Fin k → Finset (Fin m → Fin (k+1)),
        (∀ i, Commons.Combinatorics.Ramsey.IsInsens i (Ds i)) ∧
        D = Finset.univ.filter (fun x => ∀ i, x ∈ Ds i)) ∧
      γ * (((k+1 : ℕ) : ℝ) ^ m) ≤ (D.card : ℝ) ∧
      (δ + γ) * (D.card : ℝ) ≤ ((A ∩ D).card : ℝ) := by
  classical
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hηpos : 0 < η := by rw [hη]; positivity
  have hηle1 : η ≤ 1 := by rw [hη]; nlinarith only [hδ.le, hδ1, hθ.le, hθ1]
  have hγnn : 0 ≤ γ := by rw [hγ]; positivity
  have hγle : γ ≤ η^2/2 := by
    rw [hγ, div_le_iff₀ hk0]
    nlinarith only [hδ1, sq_nonneg η, hkR]
  have hγle1 : γ ≤ 1 := by
    have h1 : η^2 ≤ 1 := by nlinarith only [hηle1, hηpos]
    linarith only [hγle, h1]
  have hγle3 : γ ≤ 3*η := by
    rw [hγ, div_le_iff₀ hk0]
    nlinarith only [hδ1, hηle1, hηpos, hkR, sq_nonneg η]
  have hδθ : δ * θ = 48 * η := by rw [hη]; ring
  have hδ3 : 0 < δ - 3*η := by
    have h1 : 3*η ≤ δ/16 := by rw [hη]; nlinarith only [hθ1, hδ.le, hθ.le]
    linarith
  have hXnn : (0:ℝ) ≤ (((k+1 : ℕ) : ℝ))^m := by positivity
  set N : ℝ := (((k+1 : ℕ) : ℝ))^m with hN
  have hNpos : 0 < N := by rw [hN]; positivity
  have hnK : ((k:ℝ)^m) ≤ η * N := by rw [hN]; exact hm
  have hden' : (δ - 2*η) * N ≤ (A.card : ℝ) := by rw [hN]; exact hA
  have hlines' : (θ/2) * (N - ((k:ℝ)^m))
      ≤ (((varWord k m).filter (fun g => ∀ v : Fin k, linePt g v ∈ A)).card : ℝ) := by
    rw [hN]; exact hlines
  -- the insensitive sets `Cᵢ` and their intersection `C`
  let Ci : Fin k → Finset (Fin m → Fin (k+1)) :=
    fun i => Finset.univ.filter (fun x => replTop i x ∈ A)
  let C : Finset (Fin m → Fin (k+1)) := Finset.univ.filter (fun x => ∀ i, x ∈ Ci i)
  have hmemCi : ∀ (i : Fin k) (x : Fin m → Fin (k+1)), x ∈ Ci i ↔ replTop i x ∈ A := by
    intro i x; simp [Ci]
  have hmemC : ∀ x : Fin m → Fin (k+1), x ∈ C ↔ ∀ i, x ∈ Ci i := by
    intro x; simp [C]
  -- the set of "good" lines
  set G := (varWord k m).filter (fun g => ∀ v : Fin k, linePt g v ∈ A) with hG
  have hlinesG : (θ/2) * (N - ((k:ℝ)^m)) ≤ (G.card : ℝ) := by rw [hG]; exact hlines'
  have hGC : (G.card : ℝ) ≤ (C.card : ℝ) := by
    have h1 : G.card ≤ C.card := by
      refine Finset.card_le_card_of_injOn (topPt (k := k) (n := m)) ?_ ?_
      · intro g hg
        simp only [Finset.mem_coe, hG, Finset.mem_filter] at hg
        rw [Finset.mem_coe, hmemC]
        intro i
        rw [hmemCi, replTop_topPt]
        exact hg.2 i
      · intro g _ h _ hgh
        exact topPt_injective k m hgh
    exact_mod_cast h1
  have hGlower : (θ/2) * (N - ((k:ℝ)^m)) ≤ (C.card : ℝ) := le_trans hlinesG hGC
  -- `|C| ≥ (θ/4) N`
  have hCbound : (θ/4) * N ≤ (C.card : ℝ) := by
    have h1 : (1 - η) * N ≤ N - ((k:ℝ)^m) := by linarith [hnK]
    have h2 : (θ/2) * ((1-η) * N) ≤ (C.card : ℝ) := by
      have := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ θ/2)
      linarith [this, hGlower]
    have h3 : (θ/4) * N ≤ (θ/2) * ((1-η)*N) := by
      have hηhalf : η ≤ 1/2 := by linarith
      have hθN : 0 ≤ θ * N := mul_nonneg hθ.le hNpos.le
      nlinarith only [hθN, hηhalf]
    linarith [h2, h3]
  -- `A ∩ C` consists of top-free points
  have hACtop : A ∩ C ⊆ (Finset.univ : Finset (Fin m → Fin (k+1))).filter
      (fun x => ∀ j, x j ≠ Fin.last k) := by
    intro x hx
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨hxA, hxC⟩ := hx
    by_contra hcon
    push_neg at hcon
    obtain ⟨j0, hj0⟩ := hcon
    exact hno (exists_line_of_top A ⟨j0, hj0⟩ hxA
      (fun i => (hmemCi i x).mp ((hmemC x).mp hxC i)))
  have hACcard : ((A ∩ C).card : ℝ) ≤ η * N := by
    have h1 : (A ∩ C).card ≤ k^m := by
      calc (A ∩ C).card ≤ ((Finset.univ : Finset (Fin m → Fin (k+1))).filter
            (fun x => ∀ j, x j ≠ Fin.last k)).card := Finset.card_le_card hACtop
        _ = k^m := card_noTop k m
    calc ((A ∩ C).card : ℝ) ≤ ((k^m : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (k:ℝ)^m := by push_cast; ring
      _ ≤ η * N := hnK
  -- `|Cᶜ| = N - |C|`, hence `|Cᶜ| ≤ (1 - θ/4) N`
  have hcompl : ((Cᶜ).card : ℝ) = N - (C.card : ℝ) := by
    have hle : C.card ≤ (k+1)^m := by
      have := Finset.card_le_univ C
      simpa [Fintype.card_fun] using this
    rw [Finset.card_compl, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      Nat.cast_sub hle, hN]
    push_cast; ring
  have hWC : ((Cᶜ).card : ℝ) ≤ (1 - θ/4) * N := by
    rw [hcompl]; nlinarith only [hCbound]
  -- `|A \ C| ≥ (δ - 3η) N`
  have hAUC : (δ - 3*η) * N ≤ ((A \ C).card : ℝ) := by
    have hsub : A ⊆ (A ∩ C) ∪ (A \ C) := by
      intro x hx
      by_cases h : x ∈ C
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hx, h⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hx, h⟩))
    have h1 : A.card ≤ ((A ∩ C) ∪ (A \ C)).card := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (A ∩ C) (A \ C)
    have h3 : (A.card : ℝ) ≤ ((A ∩ C).card : ℝ) + ((A \ C).card : ℝ) := by
      exact_mod_cast le_trans h1 h2
    linarith [hden', hACcard, h3]
  -- the density of `A` on `W \ C` is at least `δ + 6η`
  have hCpos : 0 < ((Cᶜ).card : ℝ) := by
    have h3 : 0 < (δ - 3*η) * N := mul_pos hδ3 hNpos
    have hsub : A \ C ⊆ Cᶜ := by
      intro x hx
      rw [Finset.mem_compl]
      exact (Finset.mem_sdiff.mp hx).2
    have h4 : ((A \ C).card : ℝ) ≤ ((Cᶜ).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    linarith [hAUC, h3, h4]
  have hratio : δ + 6*η ≤ ((A \ C).card : ℝ) / ((Cᶜ).card : ℝ) := by
    rw [le_div_iff₀ hCpos]
    have h1 : (δ + 6*η) * ((Cᶜ).card : ℝ) ≤ (δ + 6*η) * ((1 - θ/4) * N) :=
      mul_le_mul_of_nonneg_left hWC (by linarith [hδ.le, hηpos.le])
    have h2 : (δ + 6*η) * ((1 - θ/4) * N) ≤ (δ - 3*η) * N := by
      have h2a : (δ + 6*η) * (1 - θ/4) ≤ δ - 3*η := by
        nlinarith only [hδθ, hθ.le, hηpos.le, hδ.le]
      calc (δ + 6*η) * ((1 - θ/4) * N) = ((δ + 6*η) * (1 - θ/4)) * N := by ring
        _ ≤ (δ - 3*η) * N := mul_le_mul_of_nonneg_right h2a hNpos.le
    linarith [h1, h2, hAUC]
  -- the first-violation partition of `W \ C`
  let part : Fin k → Finset (Fin m → Fin (k+1)) :=
    fun i => Finset.univ.filter (fun x => x ∉ Ci i ∧ ∀ j, j < i → x ∈ Ci j)
  have hdisj : ∀ i j : Fin k, i ≠ j → Disjoint (part i) (part j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have hxi' := (Finset.mem_filter.mp hxi).2
    have hxj' := (Finset.mem_filter.mp hxj).2
    rcases lt_or_gt_of_ne hij with h | h
    · exact hxi'.1 (hxj'.2 i h)
    · exact hxj'.1 (hxi'.2 j h)
  have hcover : (Finset.univ : Finset (Fin m → Fin (k+1))).filter
        (fun x => ∃ i : Fin k, x ∉ Ci i) = Finset.univ.biUnion part := by
    ext x
    simp only [part, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · rintro ⟨i0, hi0⟩
      set S := Finset.univ.filter (fun i : Fin k => x ∉ Ci i) with hS
      have hne : S.Nonempty := ⟨i0, by simp [hS, hi0]⟩
      have hminmem : S.min' hne ∈ S := Finset.min'_mem S hne
      have hmin := (Finset.mem_filter.mp hminmem).2
      refine ⟨S.min' hne, hmin, ?_⟩
      intro j hj
      by_contra hjc
      have hjS : j ∈ S := by simp [hS, hjc]
      have := Finset.min'_le S j hjS
      exact absurd hj (not_lt.mpr this)
    · rintro ⟨i, h1, _⟩
      exact ⟨i, h1⟩
  have hunion : Finset.univ.biUnion part = Cᶜ := by
    rw [← hcover]
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, hmemC]
    constructor
    · rintro ⟨i, hi⟩ hC
      exact hi (hC i)
    · intro hx
      by_contra hcon
      push_neg at hcon
      exact hx hcon
  -- the two sum identities
  have hsumM : ∑ i : Fin k, ((part i).card : ℝ) = ((Cᶜ).card : ℝ) := by
    have hnat : (Finset.univ.biUnion part).card = ∑ i : Fin k, (part i).card := by
      rw [Finset.card_biUnion (fun i _ j _ hij => hdisj i j hij)]
    have hcast : ((Finset.univ.biUnion part).card : ℝ) = ∑ i : Fin k, ((part i).card : ℝ) := by
      rw [hnat]; push_cast; ring
    rw [hunion] at hcast
    exact hcast.symm
  have hsumA : ∑ i : Fin k, ((A ∩ part i).card : ℝ) = ((A \ C).card : ℝ) := by
    have hdisjA : ∀ i j : Fin k, i ≠ j → Disjoint (A ∩ part i) (A ∩ part j) := fun i j hij =>
      Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right (hdisj i j hij)
    have hnat : (Finset.univ.biUnion (fun i => A ∩ part i)).card
        = ∑ i : Fin k, (A ∩ part i).card := by
      rw [Finset.card_biUnion (fun i _ j _ hij => hdisjA i j hij)]
    have hunionA : Finset.univ.biUnion (fun i => A ∩ part i) = A \ C := by
      have h1 : Finset.univ.biUnion (fun i => A ∩ part i)
          = A ∩ Finset.univ.biUnion part := by
        ext x
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_inter]
        constructor
        · rintro ⟨i, hxA, hxp⟩
          exact ⟨hxA, ⟨i, hxp⟩⟩
        · rintro ⟨hxA, i, hxp⟩
          exact ⟨i, hxA, hxp⟩
      rw [h1, hunion]
      ext x
      simp only [Finset.mem_inter, Finset.mem_compl, Finset.mem_sdiff]
    have hcast : ((Finset.univ.biUnion (fun i => A ∩ part i)).card : ℝ)
        = ∑ i : Fin k, ((A ∩ part i).card : ℝ) := by
      rw [hnat]; push_cast; ring
    rw [hunionA] at hcast
    exact hcast.symm
  -- the pigeonhole step
  have hratio' : (δ + 6*η) * ((Cᶜ).card : ℝ) ≤ ((A \ C).card : ℝ) := by
    rw [le_div_iff₀ hCpos] at hratio
    exact hratio
  have hkey : (δ + 3*η + (3*η/k) * (Fintype.card (Fin k) : ℝ)) * ((Cᶜ).card : ℝ)
      ≤ ((A \ C).card : ℝ) := by
    have hcard : (Fintype.card (Fin k) : ℝ) = k := by simp
    have hcalc : (3*η/k) * (k:ℝ) = 3*η := div_mul_cancel₀ (3*η) (by positivity)
    have h1 : δ + 3*η + (3*η/k) * (Fintype.card (Fin k) : ℝ) = δ + 6*η := by
      rw [hcard, hcalc]; ring
    rw [h1]; exact hratio'
  haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  obtain ⟨i₀, hi₀1, hi₀2⟩ :=
    Commons.Combinatorics.DensityIncrement.part_pigeonhole_pos (fun i : Fin k => ((part i).card : ℝ))
    (fun i : Fin k => ((A ∩ part i).card : ℝ)) ((Cᶜ).card : ℝ) ((A \ C).card : ℝ)
    (δ + 3*η) (3*η/k) (fun i => Nat.cast_nonneg _)
    (fun i => by exact_mod_cast Finset.card_le_card Finset.inter_subset_right)
    hsumM hsumA (Nat.cast_nonneg _) (div_nonneg (by linarith [hηpos.le]) hk0.le)
    (by linarith [hδ.le, hηpos.le]) hkey
  -- the final set
  let Ds : Fin k → Finset (Fin m → Fin (k+1)) :=
    fun i => if i = i₀ then (Ci i₀)ᶜ else if i < i₀ then Ci i else Finset.univ
  let D : Finset (Fin m → Fin (k+1)) := Finset.univ.filter (fun x => ∀ i, x ∈ Ds i)
  have hD : D = part i₀ := by
    ext x
    simp only [D, Ds, part, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · have h' : x ∈ (Ci i₀)ᶜ := by simpa using h i₀
        exact Finset.mem_compl.mp h'
      · intro j hj
        have h' : x ∈ Ci j := by
          simpa only [if_neg (ne_of_lt hj), if_pos hj] using h j
        exact h'
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i = i₀
      · subst hi
        simpa using h1
      · by_cases hj : i < i₀
        · simpa only [if_neg hi, if_pos hj] using h2 i hj
        · rw [if_neg hi, if_neg hj]
          exact Finset.mem_univ x
  refine ⟨D, ⟨Ds, ?_, rfl⟩, ?_, ?_⟩
  · intro i
    by_cases hi : i = i₀
    · have hDs : Ds i = (Ci i)ᶜ := by
        rw [show Ds i = (Ci i₀)ᶜ from by simp only [Ds]; exact if_pos hi, hi]
      rw [hDs]
      exact IsInsens.compl (isInsens_replTop i A)
    · by_cases hj : i < i₀
      · simp only [Ds, if_neg hi, if_pos hj]
        exact isInsens_replTop i A
      · simp only [Ds, if_neg hi, if_neg hj]
        exact isInsens_univ k m i
  · rw [hD]
    have hMbound : (δ - 3*η) * N ≤ ((Cᶜ).card : ℝ) := by
      have hsub : A \ C ⊆ Cᶜ := by
        intro x hx
        rw [Finset.mem_compl]
        exact (Finset.mem_sdiff.mp hx).2
      have h4 : ((A \ C).card : ℝ) ≤ ((Cᶜ).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      linarith [hAUC, h4]
    have h3ηk : (0:ℝ) ≤ 3*η/k := by positivity
    have hbig : (3*η/k) * ((δ - 3*η)*N) ≤ ((part i₀).card : ℝ) := by
      have h5 := mul_le_mul_of_nonneg_left hMbound h3ηk
      linarith [h5, hi₀1]
    have hγle : γ ≤ (3*η/k) * (δ - 3*η) := by
      have h1 : 3*η ≤ δ/16 := by rw [hη]; nlinarith only [hθ1, hδ.le, hθ.le]
      have hmain : δ * η^2 ≤ 3*η*(δ-3*η) := by
        nlinarith only [hδ1, hηle1, hηpos, hδθ, hδ.le, h1]
      rw [hγ]
      calc δ * η^2 / k = (δ * η^2) / k := rfl
        _ ≤ (3*η*(δ-3*η)) / k := div_le_div_of_nonneg_right hmain hk0.le
        _ = (3*η/k) * (δ-3*η) := by ring
    have h6 : γ * N ≤ (3*η/k) * (δ - 3*η) * N := by
      have := mul_le_mul_of_nonneg_right hγle hNpos.le
      linarith [this]
    linarith [hbig, h6]
  · rw [hD]
    have hδγ : δ + γ ≤ δ + 3*η := by linarith [hγle3]
    have h7 : (δ + γ) * ((part i₀).card : ℝ) ≤ (δ + 3*η) * ((part i₀).card : ℝ) :=
      mul_le_mul_of_nonneg_right hδγ (Nat.cast_nonneg _)
    linarith [h7, hi₀2]

/-- **Correlation lemma.**  Under the density-increment dichotomy of Dodos–Kanellopoulos–Tyros,
a line-free set `A ⊆ [k+1]^m` of density at least `δ - 2η` is correlated with a large set `D` which
is an intersection of `(i, k+1)`-insensitive sets: `|D| ≥ γ (k+1)^m` and `|A ∩ D| ≥ (δ+γ)|D|`. -/
theorem dkt_insens_correlation (k : ℕ) (hk : 2 ≤ k) (δ θ η γ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hη : η = δ * θ / 48) (hγ : γ = δ * η^2 / k)
    (m : ℕ) (hm1 : 1 ≤ m) (hm : ((k : ℝ) ^ m) ≤ η * (((k+1 : ℕ) : ℝ) ^ m))
    (A : Finset (Fin m → Fin (k+1)))
    (hA : (δ - 2*η) * (((k+1 : ℕ) : ℝ)) ^ m ≤ (A.card : ℝ))
    (hno : ¬ ∃ l : _root_.Combinatorics.Line (Fin (k+1)) (Fin m), ∀ v : Fin (k+1), l v ∈ A)
    (hcase : (δ + η^2/2) * (((k+1 : ℕ) : ℝ)) ^ m ≤ (A.card : ℝ) ∨
       (θ/2) * ((((k+1 : ℕ) : ℝ) ^ m) - ((k : ℝ) ^ m)) ≤
         (((Commons.Combinatorics.Ramsey.varWord k m).filter
           (fun g => ∀ v : Fin k, Commons.Combinatorics.Ramsey.linePt g v ∈ A)).card : ℝ)) :
    ∃ D : Finset (Fin m → Fin (k+1)),
      (∃ Ds : Fin k → Finset (Fin m → Fin (k+1)),
        (∀ i, Commons.Combinatorics.Ramsey.IsInsens i (Ds i)) ∧
        D = Finset.univ.filter (fun x => ∀ i, x ∈ Ds i)) ∧
      γ * (((k+1 : ℕ) : ℝ) ^ m) ≤ (D.card : ℝ) ∧
      (δ + γ) * (D.card : ℝ) ≤ ((A ∩ D).card : ℝ) := by
  rcases hcase with hinc | hlines
  · -- `A` is denser than `δ + η²/2`, hence denser than `δ`: the first alternative of
    -- `dkt_core_insens` applies directly.
    have hδ_le : δ * (((k+1 : ℕ) : ℝ)) ^ m ≤ (δ + η^2/2) * (((k+1 : ℕ) : ℝ)) ^ m := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith [sq_nonneg η]
    exact dkt_core_insens k hk δ θ η γ hδ hδ1 hθ hθ1 hη hγ m hm1 hm A
      (le_trans hδ_le hinc) hno (Or.inl hinc)
  · -- The many-lines alternative; here the weak density hypothesis is genuinely used.
    exact dkt_insens_correlation_lines k hk δ θ η γ hδ hδ1 hθ hθ1 hη hγ m hm1 hm A hA hno hlines

end Commons.Combinatorics.Ramsey
