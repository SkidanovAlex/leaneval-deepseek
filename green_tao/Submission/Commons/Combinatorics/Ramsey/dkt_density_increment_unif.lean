import Mathlib
import Submission.Commons.Combinatorics.Ramsey.dkt_density_increment

set_option maxHeartbeats 1000000

open Finset
open _root_.Combinatorics

namespace Commons.Combinatorics.Ramsey

noncomputable section

/-- Uniform version of `exists_subspace_dense_slices`: for all `ε ≥ ε₀` the same threshold `n₀`
works. -/
lemma dense_slices_uniform (K m : ℕ) (hK : 2 ≤ K) (hm : 1 ≤ m) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ ε : ℝ, ε₀ ≤ ε → ε < 1 →
      ∀ A : Finset (Fin n → Fin K), ε * (K : ℝ) ^ n < (A.card : ℝ) →
      ∃ l : ℕ, ∃ h : l < n, ∃ V : _root_.Combinatorics.Subspace (Fin m) (Fin K) (Fin l),
        ∀ x : Fin m → Fin K,
          ((A.card : ℝ) / (K : ℝ) ^ n - ε) * ((K : ℝ) ^ (n - l)) ≤
            (((Finset.univ : Finset (Fin (n - l) → Fin K)).filter
               (fun y => _root_.Commons.Combinatorics.Ramsey.cat (le_of_lt h) (V x) y ∈ A)).card : ℝ) := by
  refine ⟨Nat.ceil ((K:ℝ)^m * m / ε₀), ?_⟩
  intro n hn ε hε0 hε1 A hA
  have hεpos : 0 < ε := lt_of_lt_of_le hε₀ hε0
  have hn' : (K:ℝ)^m * m / ε ≤ (n:ℝ) := by
    have h1 : (K:ℝ)^m * m / ε ≤ (K:ℝ)^m * m / ε₀ :=
      div_le_div_of_nonneg_left (by positivity) hε₀ hε0
    have h2 : (K:ℝ)^m * m / ε₀ ≤ (n:ℝ) := Nat.ceil_le.mp hn
    linarith
  exact dense_slices_aux hK hm ε hεpos hε1 A hA hn'

/-- The DKT dichotomy, uniformly in the density threshold `δ' ≥ δ`. -/
lemma dkt_dichotomy_uniform (k : ℕ) (hk : 2 ≤ k)
    (hgr : ∀ (M : ℕ), ∃ n : ℕ, ∀ n' : ℕ, n ≤ n' → ∀ C : _root_.Combinatorics.Line (Fin k) (Fin n') → Fin 2,
      ∃ S : _root_.Combinatorics.Subspace (Fin M) (Fin k) (Fin n'), ∃ c : Fin 2,
        ∀ σ : Fin M → Option (Fin k), (hσ : ∃ e, σ e = none) →
          C ⟨fun i => Sum.elim (fun a => some a) σ (S.idxFun i), by
              obtain ⟨e, he⟩ := hσ; obtain ⟨i, hi⟩ := S.proper e
              exact ⟨i, by simp [hi, he]⟩⟩ = c)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀)
    (hdhj₀ : ∀ n : ℕ, m₀ ≤ n → ∀ T : Finset (Fin n → Fin k),
      (δ / 4) * (k : ℝ) ^ n ≤ (T.card : ℝ) →
        ∃ l : _root_.Combinatorics.Line (Fin k) (Fin n), ∀ x : Fin k, l x ∈ T)
    (hθm : θ * (((k+1 : ℕ) : ℝ) ^ m₀ - (k : ℝ) ^ m₀) ≤ δ / 4)
    (m : ℕ) (hm : m₀ ≤ m) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ δ' : ℝ, δ ≤ δ' → δ' ≤ 1 →
      ∀ A : Finset (Fin n → Fin (k+1)), δ' * (((k+1 : ℕ) : ℝ)) ^ n ≤ (A.card : ℝ) →
      (∃ X : _root_.Combinatorics.Subspace (Fin m) (Fin (k+1)) (Fin n),
          (δ' + (δ' * θ / 48)^2/2) * (((k+1 : ℕ) : ℝ)) ^ m ≤
            ((Finset.univ : Finset (Fin m → Fin (k+1))).filter (fun x => X x ∈ A)).card) ∨
      (∃ W : _root_.Combinatorics.Subspace (Fin m) (Fin (k+1)) (Fin n),
          (δ' - 2*(δ' * θ / 48)) * (((k+1 : ℕ) : ℝ)) ^ m ≤
            ((Finset.univ : Finset (Fin m → Fin (k+1))).filter (fun x => W x ∈ A)).card ∧
          (θ/2) * ((((k+1 : ℕ) : ℝ) ^ m) - ((k : ℝ) ^ m)) ≤
            (((Commons.Combinatorics.Ramsey.varWord k m).filter
              (fun g => ∀ v : Fin k, W (Commons.Combinatorics.Ramsey.linePt g v) ∈ A)).card : ℝ)) := by
  classical
  obtain ⟨ngr, hngr⟩ := hgr m
  set M : ℕ := max (max 1 ngr) m with hMdef
  have hMngr : ngr ≤ M := by rw [hMdef]; omega
  have hM1 : 1 ≤ M := by rw [hMdef]; omega
  have hMm : m ≤ M := by rw [hMdef]; omega
  have hε₀pos : 0 < (δ * θ / 48)^2/2 := by positivity
  obtain ⟨n₀, hn₀⟩ := dense_slices_uniform (k+1) M (by omega) hM1 ((δ*θ/48)^2/2) hε₀pos
  refine ⟨n₀, fun n hn δ' hδ' hδ'1 A hA => ?_⟩
  set η : ℝ := δ' * θ / 48 with hηdef
  set ε : ℝ := η^2/2 with hεdef
  have hδ'pos : 0 < δ' := lt_of_lt_of_le hδ hδ'
  have hη0 : 0 < η := by rw [hηdef]; positivity
  have hηθ : η < θ / 2 := by
    rw [hηdef]
    nlinarith [hδ', hδ'1, hθ, hθ1]
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hε1 : ε < 1 := by
    rw [hεdef]
    have h1 : η ≤ 1/48 := by rw [hηdef]; nlinarith [hδ'pos, hδ'1, hθ, hθ1]
    nlinarith [hη0, h1]
  have hεδ : ε < δ' := by
    rw [hεdef]
    have h1 : η ≤ δ'/48 := by rw [hηdef]; nlinarith [hδ'pos, hδ'1, hθ, hθ1]
    nlinarith [hδ'pos, hδ'1, hη0, h1]
  have hεge : (δ*θ/48)^2/2 ≤ ε := by
    rw [hεdef, hηdef]
    have hle : δ * θ / 48 ≤ δ' * θ / 48 := by
      have := mul_le_mul_of_nonneg_right hδ' (le_of_lt hθ); linarith
    have hsq : (δ * θ / 48)^2 ≤ (δ' * θ / 48)^2 :=
      pow_le_pow_left₀ (by positivity) hle 2
    linarith
  have hqn : (0:ℝ) < (((k+1 : ℕ) : ℝ)) ^ n := by positivity
  have hAε : ε * (((k+1 : ℕ) : ℝ)) ^ n < (A.card : ℝ) := by
    have h1 := mul_lt_mul_of_pos_right hεδ hqn
    linarith [hA, h1]
  obtain ⟨l, hl, V, hV⟩ := hn₀ n hn ε hεge hε1 A hAε
  have hdens : δ' ≤ (A.card : ℝ) / (((k+1 : ℕ) : ℝ)) ^ n := by
    rw [le_div_iff₀ hqn]; exact hA
  have hV' : ∀ x : Fin M → Fin (k+1), (δ' - η^2/2) * (((k+1 : ℕ) : ℝ) ^ (n - l)) ≤
      (((Finset.univ : Finset (Fin (n-l) → Fin (k+1))).filter
          (fun y => cat (le_of_lt hl) (V x) y ∈ A)).card : ℝ) := by
    intro x
    have h1 := hV x
    have h2 : δ' - η^2/2 ≤ (A.card : ℝ) / (((k+1 : ℕ) : ℝ) ^ n) - ε := by
      rw [hεdef]; linarith
    have h3 : (0:ℝ) ≤ (((k+1 : ℕ) : ℝ) ^ (n - l)) := by positivity
    have h4 := mul_le_mul_of_nonneg_right h2 h3
    linarith [h1, h4]
  have hdhj₀' : ∀ n' : ℕ, m₀ ≤ n' → ∀ T : Finset (Fin n' → Fin k),
      (δ' / 4) * (k : ℝ) ^ n' ≤ (T.card : ℝ) →
        ∃ l' : _root_.Combinatorics.Line (Fin k) (Fin n'), ∀ x : Fin k, l' x ∈ T := by
    intro n' hn' T hT
    refine hdhj₀ n' hn' T (le_trans ?_ hT)
    have hknn : (0:ℝ) ≤ (k:ℝ)^n' := by positivity
    exact mul_le_mul_of_nonneg_right (by linarith [hδ'] : δ / 4 ≤ δ' / 4) hknn
  have hθm' : θ * (((k+1 : ℕ) : ℝ) ^ m₀ - (k : ℝ) ^ m₀) ≤ δ' / 4 :=
    le_trans hθm (by linarith [hδ'])
  let C : _root_.Combinatorics.Line (Fin k) (Fin M) → Fin 2 :=
    fun L => if goodLine k M l n θ A V hl L.idxFun then 0 else 1
  obtain ⟨S, c, hSc⟩ := hngr M hMngr C
  have hmono : ∀ σ : Fin m → Option (Fin k), (∃ e, σ e = none) →
      (goodLine k M l n θ A V hl (substIdx M m k S σ) ↔ c = 0) := by
    intro σ hσ
    have h := hSc σ hσ
    change (if goodLine k M l n θ A V hl
        (fun i => Sum.elim (fun a => some a) σ (S.idxFun i)) then (0:Fin 2) else 1) = c at h
    rw [← substIdx_eq M m k S σ] at h
    constructor
    · intro hg; rw [if_pos hg] at h; exact h.symm
    · intro hc; by_contra hg; rw [hc] at h; rw [if_neg hg] at h
      exact Fin.zero_ne_one h.symm
  obtain ⟨σ₀, hσ₀ne, hσ₀good⟩ := dkt_exists_goodline k m m₀ M l n hk hm₀ hm δ' θ η
    hδ'pos hδ'1 hθ hθ1 hηdef hdhj₀' hθm' S V hl A hV'
  have hc0 : c = 0 := (hmono σ₀ hσ₀ne).mp hσ₀good
  have hgoodall : ∀ σ : Fin m → Option (Fin k), (∃ e, σ e = none) →
      goodLine k M l n θ A V hl (substIdx M m k S σ) :=
    fun σ hσ => (hmono σ hσ).mpr hc0
  have hUa : ∀ x : Fin m → Fin (k+1), (δ' - η^2/2) * (((k+1 : ℕ) : ℝ) ^ (n - l)) ≤
      (((Finset.univ : Finset (Fin (n-l) → Fin (k+1))).filter
          (fun y => cat (le_of_lt hl) (compSub V (liftSub M m k S) x) y ∈ A)).card : ℝ) := by
    intro x
    have h1 := hV' (liftSub M m k S x)
    rw [compSub_apply]
    exact h1
  have hUb : ∀ g ∈ varWord k m, θ * (((k+1 : ℕ) : ℝ) ^ (n - l)) ≤
      (((Finset.univ : Finset (Fin (n-l) → Fin (k+1))).filter
          (fun y => ∀ v : Fin k,
            cat (le_of_lt hl) (compSub V (liftSub M m k S) (linePt g v)) y ∈ A)).card : ℝ) := by
    intro g hg
    have h1 := hgoodall g (mem_varWord.mp hg)
    have hfe : (Finset.univ.filter (fun y : Fin (n-l) → Fin (k+1) =>
          ∀ v : Fin k, cat (le_of_lt hl) (compSub V (liftSub M m k S) (linePt g v)) y ∈ A))
        = (Finset.univ.filter (fun y : Fin (n-l) → Fin (k+1) =>
          ∀ v : Fin k, cat (le_of_lt hl) (V (linePt (substIdx M m k S g) v)) y ∈ A)) := by
      apply Finset.filter_congr
      intro y _
      constructor
      · intro hx v
        have := hx v
        rwa [compSub_apply, liftSub_linePt] at this
      · intro hx v
        rw [compSub_apply, liftSub_linePt]
        exact hx v
    rw [hfe]
    exact h1
  by_cases hX : ∃ X : _root_.Combinatorics.Subspace (Fin m) (Fin (k+1)) (Fin n),
      (δ' + η^2/2) * (((k+1 : ℕ) : ℝ) ^ m) ≤
        ((Finset.univ : Finset (Fin m → Fin (k+1))).filter (fun x => X x ∈ A)).card
  · exact Or.inl (by simpa only [hηdef] using hX)
  · refine Or.inr ?_
    push_neg at hX
    exact by
      simpa only [hηdef] using dkt_w_from_u k m l n hk (by omega) hl δ' θ η hδ'pos hθ hθ1 hη0 hηθ A
        (compSub V (liftSub M m k S)) hUa hUb hX


/-- **Uniform density increment for the Hales–Jewett cube.** Assuming the density Hales–Jewett
theorem for the alphabet `Fin k` and the Graham–Rothschild statement `hgr` for combinatorial
lines, a subset of `[k+1]^n` of density at least `δ` either contains a combinatorial line, or
has density exceeding its own density by a fixed `γ > 0` on some `d0`-dimensional subspace. -/
theorem dkt_density_increment_unif (k : ℕ) (hk : 1 ≤ k)
    (hdhj : ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ T : Finset (Fin n → Fin k),
      δ * (k : ℝ) ^ n ≤ (T.card : ℝ) →
        ∃ l : Combinatorics.Line (Fin k) (Fin n), ∀ x : Fin k, l x ∈ T)
    (hgr : ∀ (M : ℕ), ∃ n : ℕ, ∀ n' : ℕ, n ≤ n' → ∀ C : Combinatorics.Line (Fin k) (Fin n') → Fin 2,
      ∃ S : Combinatorics.Subspace (Fin M) (Fin k) (Fin n'), ∃ c : Fin 2,
        ∀ σ : Fin M → Option (Fin k), (hσ : ∃ e, σ e = none) →
          C ⟨fun i => Sum.elim (fun a => some a) σ (S.idxFun i), by
              obtain ⟨e, he⟩ := hσ; obtain ⟨i, hi⟩ := S.proper e
              exact ⟨i, by simp [hi, he]⟩⟩ = c) :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ γ : ℝ, 0 < γ ∧ ∀ d0 : ℕ, 1 ≤ d0 → ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n → ∀ T : Finset (Fin n → Fin (k+1)),
        δ * ((k+1 : ℕ) : ℝ) ^ n ≤ (T.card : ℝ) →
        (∃ l : Combinatorics.Line (Fin (k+1)) (Fin n), ∀ x : Fin (k+1), l x ∈ T) ∨
        ∃ S : Combinatorics.Subspace (Fin d0) (Fin (k+1)) (Fin n),
          (T.card : ℝ) * ((k+1 : ℕ) : ℝ) ^ d0 + γ * ((k+1 : ℕ) : ℝ) ^ (n + d0)
            ≤ ((Finset.univ : Finset (Fin d0 → Fin (k+1))).filter (fun x => S x ∈ T)).card
                * ((k+1 : ℕ) : ℝ) ^ n := by
  intro δ hδ hδ1
  rcases eq_or_lt_of_le hk with hk1 | hk2
  · -- alphabet `Fin 1`: any two points form a line
    subst hk1
    obtain ⟨n₁, hn₁⟩ := _root_.Commons.Combinatorics.Additive.Szemeredi.dhj_two δ hδ
    refine ⟨δ/2, by linarith, ?_⟩
    intro d0 hd0
    refine ⟨max n₁ 1, ?_⟩
    intro n hn T hT
    refine Or.inl ?_
    obtain ⟨w, P, hP, hw⟩ := hn₁ n (le_trans (le_max_left _ _) hn) T hT
    refine ⟨⟨fun i => if i ∈ P then none else some (w i), ?_⟩, fun v => ?_⟩
    · obtain ⟨i, hi⟩ := hP
      exact ⟨i, by simp [hi]⟩
    · have h1 : (fun i => (if i ∈ P then (none : Option (Fin (1+1))) else some (w i)).getD v)
          = (fun i => if i ∈ P then v else w i) := by
        funext i
        by_cases h : i ∈ P <;> simp [h]
      show (fun i => (if i ∈ P then (none : Option (Fin (1+1))) else some (w i)).getD v) ∈ T
      rw [h1]
      exact hw v
  · -- alphabet `Fin (k+1)`, `k ≥ 2`
    obtain ⟨m₀', hm₀'⟩ := hdhj (δ/4) (by linarith)
    set m₀ : ℕ := max m₀' 1 with hm₀def
    have hm₀1 : 1 ≤ m₀ := le_max_right _ _
    have hm₀_thr : ∀ n : ℕ, m₀ ≤ n → ∀ T : Finset (Fin n → Fin k),
        (δ/4) * (k : ℝ)^n ≤ (T.card : ℝ) → ∃ l : Line (Fin k) (Fin n), ∀ x, l x ∈ T := by
      intro n hn T hT
      exact hm₀' n (le_trans (le_max_left _ _) hn) T hT
    have hKk : (0:ℝ) < (((k+1:ℕ):ℝ))^m₀ - (k:ℝ)^m₀ := by
      have h2 : ((k:ℝ)) < ((k+1:ℕ):ℝ) := by push_cast; linarith
      have h1 : (k:ℝ)^m₀ < (((k+1:ℕ):ℝ))^m₀ :=
        pow_lt_pow_left₀ h2 (by positivity) (by omega)
      linarith
    set θ : ℝ := min ((δ/4) / ((((k+1:ℕ):ℝ))^m₀ - (k:ℝ)^m₀)) 1 with hθdef
    have hθpos : 0 < θ := lt_min (div_pos (by linarith) hKk) one_pos
    have hθ1 : θ ≤ 1 := min_le_right _ _
    have hθm : θ * ((((k+1:ℕ):ℝ))^m₀ - (k:ℝ)^m₀) ≤ δ/4 := by
      have h1 : θ ≤ (δ/4) / ((((k+1:ℕ):ℝ))^m₀ - (k:ℝ)^m₀) := min_le_left _ _
      have h2 : ((δ/4) / ((((k+1:ℕ):ℝ))^m₀ - (k:ℝ)^m₀)) * ((((k+1:ℕ):ℝ))^m₀ - (k:ℝ)^m₀)
          = δ/4 := div_mul_cancel₀ _ hKk.ne'
      calc θ * ((((k+1:ℕ):ℝ))^m₀ - (k:ℝ)^m₀)
          ≤ ((δ/4) / ((((k+1:ℕ):ℝ))^m₀ - (k:ℝ)^m₀)) * ((((k+1:ℕ):ℝ))^m₀ - (k:ℝ)^m₀) :=
            mul_le_mul_of_nonneg_right h1 hKk.le
        _ = δ/4 := h2
    -- the numerical parameters attached to the *base* density `δ`
    set η₀ : ℝ := δ * θ / 48 with hη₀def
    set γ₀ : ℝ := δ * η₀^2 / k with hγ₀def
    have hη₀pos : 0 < η₀ := by rw [hη₀def]; positivity
    have hγ₀pos : 0 < γ₀ := by rw [hγ₀def]; positivity
    have hη₀_le : η₀ ≤ 1/48 := by rw [hη₀def]; nlinarith [hδ, hδ1, hθpos, hθ1]
    have hγ₀_le_one : γ₀ ≤ 1 := by
      rw [hγ₀def]
      have hk2' : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
      have hη2 : η₀^2 ≤ 1 := by nlinarith [hη₀_le, hη₀pos]
      have hδk : δ / (k:ℝ) ≤ 1 := by
        rw [div_le_one (by positivity : (0:ℝ) < (k:ℝ))]
        linarith [hδ1, hk2']
      calc δ * η₀^2 / (k:ℝ) = (δ / (k:ℝ)) * η₀^2 := by ring
        _ ≤ 1 * 1 := by exact mul_le_mul hδk hη2 (by positivity) (by norm_num)
        _ = 1 := by ring
    set β₀ : ℝ := γ₀^2/(4*k) with hβ₀def
    have hβ₀pos : 0 < β₀ := by rw [hβ₀def]; positivity
    have hβ₀1 : β₀ ≤ 1 := by
      have h1 : γ₀^2 ≤ 1 := by nlinarith [hγ₀_le_one, hγ₀pos]
      have h2 : (1:ℝ) ≤ 4 * (k:ℝ) := by
        have hk2' : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
        linarith
      rw [hβ₀def, div_le_one (by positivity : (0:ℝ) < 4 * (k:ℝ))]
      linarith
    have h2kβ₀ : 2*((k:ℝ))*β₀ = γ₀^2/2 := by rw [hβ₀def]; field_simp; ring
    have hc5 : ∀ (m : ℕ), 1 ≤ m → ∀ β' : ℝ, 0 < β' → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ D : Finset (Fin n → Fin (k+1)), β' * (((k+1:ℕ):ℝ))^n ≤ (D.card : ℝ) →
          ∃ V : Subspace (Fin m) (Fin (k+1)) (Fin n),
            ∀ x : Fin m → Fin k, V (kvec x) ∈ D := by
      intro m hm β' hβ'
      by_cases hβ'1 : β' ≤ 1
      · exact dkt_c5 k (by omega) hdhj
          (fun K m hK hm ε hε hε1 => exists_subspace_dense_slices K m hK hm ε hε hε1)
          m hm β' hβ' hβ'1
      · push Not at hβ'1
        refine ⟨0, fun n _ D hD => ?_⟩
        exfalso
        have h1 : (D.card : ℝ) ≤ (((k+1:ℕ):ℝ))^n := by
          have h2 : D.card ≤ Fintype.card (Fin n → Fin (k+1)) := Finset.card_le_univ D
          rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h2
          exact_mod_cast h2
        have h3 : (0:ℝ) < (((k+1:ℕ):ℝ))^n := by positivity
        nlinarith [hD, h1, hβ'1, h3]
    obtain ⟨M₁, hM₁⟩ := dkt_exists_pow_mul_le k (by omega) hη₀pos
    -- the uniform increment
    refine ⟨γ₀/2, by linarith, ?_⟩
    intro d0 hd0
    obtain ⟨Ntil, htil0⟩ := dkt_tiling k hk2 hc5 d0 hd0 β₀ hβ₀pos hβ₀1
    set m : ℕ := m₀ + d0 + M₁ + Ntil + 1 with hmdef
    have hm_m₀ : m₀ ≤ m := by omega
    have hm_d0 : d0 ≤ m := by omega
    have hm_M₁ : M₁ ≤ m := by omega
    have hm_Ntil : Ntil ≤ m := by omega
    have hm1 : 1 ≤ m := by omega
    have hm_lam : (k:ℝ)^m ≤ η₀ * (((k+1:ℕ):ℝ))^m := hM₁ m hm_M₁
    obtain ⟨ndich, hdich⟩ :=
      dkt_dichotomy_uniform k hk2 hgr δ hδ hδ1 θ hθpos hθ1 m₀ hm₀1 hm₀_thr hθm m hm_m₀
    refine ⟨max ndich 1, ?_⟩
    intro n hn T hT
    by_cases hline : ∃ l : Line (Fin (k+1)) (Fin n), ∀ x : Fin (k+1), l x ∈ T
    · exact Or.inl hline
    · refine Or.inr ?_
      -- the actual density of `T`
      set ρ : ℝ := (T.card : ℝ) / (((k+1:ℕ):ℝ))^n with hρdef
      have hqn : (0:ℝ) < (((k+1:ℕ):ℝ))^n := by positivity
      have hρge : δ ≤ ρ := by rw [hρdef]; rw [le_div_iff₀ hqn]; linarith [hT]
      have hρ1 : ρ ≤ 1 := by
        rw [hρdef, div_le_one hqn]
        have h2 : T.card ≤ Fintype.card (Fin n → Fin (k+1)) := Finset.card_le_univ T
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h2
        exact_mod_cast h2
      have hρpos : 0 < ρ := lt_of_lt_of_le hδ hρge
      have hTρ : ρ * (((k+1:ℕ):ℝ))^n ≤ (T.card : ℝ) := by
        rw [hρdef, div_mul_cancel₀ _ (ne_of_gt hqn)]
      have htwo : 2 * ((k : ℝ)) * β₀ = γ₀^2/2 := h2kβ₀
      have hdensD_ge : γ₀^2/2 * (((k+1:ℕ):ℝ)^m) ≤ γ₀ * (((k+1:ℕ):ℝ)^m) := by
        have hle : γ₀^2/2 ≤ γ₀ := by nlinarith [hγ₀_le_one, hγ₀pos]
        exact mul_le_mul_of_nonneg_right hle (by positivity)
      -- per-`T` parameters
      set η : ℝ := ρ * θ / 48 with hηdef
      set γ : ℝ := ρ * η^2 / k with hγdef
      have hηpos : 0 < η := by rw [hηdef]; positivity
      have hγpos : 0 < γ := by rw [hγdef]; positivity
      have hη_le : η ≤ 1/48 := by rw [hηdef]; nlinarith [hρpos, hρ1, hθpos, hθ1]
      have hγ_le_one : γ ≤ 1 := by
        rw [hγdef]
        have hk2' : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
        have hη2 : η^2 ≤ 1 := by nlinarith [hη_le, hηpos]
        have hρk : ρ / (k:ℝ) ≤ 1 := by
          rw [div_le_one (by positivity : (0:ℝ) < (k:ℝ))]
          linarith [hρ1, hk2']
        calc ρ * η^2 / (k:ℝ) = (ρ / (k:ℝ)) * η^2 := by ring
          _ ≤ 1 * 1 := by exact mul_le_mul hρk hη2 (by positivity) (by norm_num)
          _ = 1 := by ring
      have hη_ge : η₀ ≤ η := by
        rw [hη₀def, hηdef]
        have h1 : δ * θ ≤ ρ * θ := mul_le_mul_of_nonneg_right hρge (le_of_lt hθpos)
        linarith
      have hγ_ge : γ₀ ≤ γ := by
        rw [hγ₀def, hγdef]
        have h2 : η₀^2 ≤ η^2 := pow_le_pow_left₀ (le_of_lt hη₀pos) hη_ge 2
        have h3 : δ * η₀^2 ≤ ρ * η^2 := by
          calc δ * η₀^2 ≤ ρ * η₀^2 := mul_le_mul_of_nonneg_right hρge (by positivity)
            _ ≤ ρ * η^2 := mul_le_mul_of_nonneg_left h2 (le_of_lt hρpos)
        exact div_le_div_of_nonneg_right h3 (by positivity)
      have hm_lam_η : (k:ℝ)^m ≤ η * (((k+1:ℕ):ℝ))^m := by
        have h1 : η₀ * (((k+1:ℕ):ℝ))^m ≤ η * (((k+1:ℕ):ℝ))^m :=
          mul_le_mul_of_nonneg_right hη_ge (by positivity)
        linarith [hm_lam, h1]
      -- the dichotomy with the actual density
      have hdich' := hdich n (le_trans (le_max_left _ _) hn) ρ hρge hρ1 T hTρ
      have hdich'' : (∃ X : Subspace (Fin m) (Fin (k+1)) (Fin n),
            (ρ + η^2/2) * (((k+1:ℕ):ℝ)^m)
              ≤ ((Finset.univ : Finset (Fin m → Fin (k+1))).filter (fun x => X x ∈ T)).card) ∨
          (∃ W : Subspace (Fin m) (Fin (k+1)) (Fin n),
            (ρ - 2*η) * (((k+1:ℕ):ℝ)^m)
              ≤ ((Finset.univ : Finset (Fin m → Fin (k+1))).filter (fun x => W x ∈ T)).card ∧
            (θ/2) * ((((k+1:ℕ):ℝ)^m) - ((k:ℝ)^m)) ≤
              (((varWord k m).filter (fun g => ∀ v : Fin k, W (linePt g v) ∈ T)).card : ℝ)) := by
        simpa only [← hηdef] using hdich'
      rcases hdich'' with ⟨X, hX⟩ | ⟨W, hW1, hW2⟩
      · -- case (i): a dense `m`-dimensional subspace
        set A : Finset (Fin m → Fin (k+1)) := dktPull X T with hAdef
        have hAno : ¬ ∃ l : Line (Fin (k+1)) (Fin m), ∀ v, l v ∈ A := by
          rw [hAdef]; exact dkt_not_line_pull X T hline
        have hA2 : (ρ - 2*η) * (((k+1:ℕ):ℝ))^m ≤ (A.card : ℝ) := by
          have hle : ρ - 2*η ≤ ρ + η^2/2 := by nlinarith [hηpos]
          have hmul := mul_le_mul_of_nonneg_right hle (by positivity : (0:ℝ) ≤ (((k+1:ℕ):ℝ))^m)
          rw [hAdef]
          simp only [dktPull]
          linarith [hX, hmul]
        have hcase : (ρ + η^2/2) * (((k+1:ℕ):ℝ))^m ≤ (A.card : ℝ) ∨
            (θ/2) * ((((k+1:ℕ):ℝ)^m) - ((k:ℝ)^m)) ≤
              (((varWord k m).filter (fun g => ∀ v : Fin k, linePt g v ∈ A)).card : ℝ) := by
          refine Or.inl ?_
          rw [hAdef]; simp only [dktPull]; exact hX
        obtain ⟨D, ⟨Ds, hinsens, hDdef⟩, hDcard, hDcorr⟩ :=
          dkt_insens_correlation k hk2 ρ θ η γ hρpos hρ1 hθpos hθ1 hηdef hγdef m hm1
            hm_lam_η A hA2 hAno hcase
        have hdensD : 2 * ((k:ℝ)) * β₀ * (((k+1:ℕ):ℝ))^m ≤ (D.card : ℝ) := by
          have h1 : (2 * ((k:ℝ)) * β₀) * (((k+1:ℕ):ℝ))^m = γ₀^2/2 * (((k+1:ℕ):ℝ))^m := by
            rw [htwo]
          rw [h1]
          have hstep : γ₀ * (((k+1:ℕ):ℝ)^m) ≤ γ * (((k+1:ℕ):ℝ)^m) :=
            mul_le_mul_of_nonneg_right hγ_ge (by positivity)
          linarith [hDcard, hdensD_ge, hstep]
        obtain ⟨VS, hVS_sub, hVS_disj, hVS_cov0⟩ := htil0 m hm_Ntil Ds hinsens D hDdef hdensD
        have hcov' : (D.card : ℝ) - γ^2/2 * (((k+1:ℕ):ℝ)^m) ≤
            ((VS.biUnion (fun S => Finset.univ.image (fun x => S x))).card : ℝ) := by
          have hγ2 : 2 * ((k:ℝ)) * β₀ ≤ γ^2/2 := by
            rw [htwo]; nlinarith [hγ_ge, hγpos]
          have hstep : 2 * ((k:ℝ)) * β₀ * (((k+1:ℕ):ℝ)^m) ≤ γ^2/2 * (((k+1:ℕ):ℝ)^m) :=
            mul_le_mul_of_nonneg_right hγ2 (by positivity)
          linarith [hVS_cov0, hstep]
        obtain ⟨V, hVmem, hVcard⟩ :=
          dktFinalStep (k := k) (d := d0) (m := m) (by omega) hγpos (by positivity)
            A D VS hDcard hDcorr hVS_sub hVS_disj hcov'
        refine ⟨scomp X V, ?_⟩
        rw [dkt_card_filter_scomp]
        have hVc := hVcard
        rw [dkt_inter_image_eq V A, Finset.card_image_of_injective _ (dkt_subspace_injective V)] at hVc
        rw [hAdef] at hVc
        -- convert the density bound into the target inequality
        have hVc' : (ρ + γ/2) * (((k+1:ℕ):ℝ)^d0)
            ≤ ((Finset.univ : Finset (Fin d0 → Fin (k+1))).filter
                (fun x => V x ∈ dktPull X T)).card := hVc
        have hmul := mul_le_mul_of_nonneg_right hVc' (le_of_lt hqn)
        have hLHS : (ρ + γ/2) * (((k+1:ℕ):ℝ)^d0) * (((k+1:ℕ):ℝ))^n
            = (T.card : ℝ) * (((k+1:ℕ):ℝ)^d0) + (γ/2) * (((k+1:ℕ):ℝ)^(n+d0)) := by
          have hρn : ρ * (((k+1:ℕ):ℝ))^n = (T.card : ℝ) := by
            rw [hρdef, div_mul_cancel₀ _ (ne_of_gt hqn)]
          have e : (((k+1:ℕ):ℝ))^d0 * (((k+1:ℕ):ℝ))^n = (((k+1:ℕ):ℝ))^(n+d0) := by
            rw [mul_comm, ← pow_add]
          calc (ρ + γ/2) * (((k+1:ℕ):ℝ)^d0) * (((k+1:ℕ):ℝ))^n
              = (ρ * (((k+1:ℕ):ℝ))^n) * (((k+1:ℕ):ℝ)^d0)
                  + (γ/2) * ((((k+1:ℕ):ℝ)^d0) * (((k+1:ℕ):ℝ))^n) := by ring
            _ = (T.card : ℝ) * (((k+1:ℕ):ℝ)^d0) + (γ/2) * (((k+1:ℕ):ℝ)^(n+d0)) := by
                  rw [hρn, e]
        have hge : γ₀/2 ≤ γ/2 := by linarith [hγ_ge]
        calc (T.card : ℝ) * (((k+1:ℕ):ℝ)^d0) + (γ₀/2) * (((k+1:ℕ):ℝ)^(n+d0))
            ≤ (T.card : ℝ) * (((k+1:ℕ):ℝ)^d0) + (γ/2) * (((k+1:ℕ):ℝ)^(n+d0)) := by
              have := mul_le_mul_of_nonneg_right hge (by positivity : (0:ℝ) ≤ (((k+1:ℕ):ℝ)^(n+d0)))
              linarith
          _ = (ρ + γ/2) * (((k+1:ℕ):ℝ)^d0) * (((k+1:ℕ):ℝ))^n := hLHS.symm
          _ ≤ ((Finset.univ : Finset (Fin d0 → Fin (k+1))).filter
                  (fun x => V x ∈ dktPull X T)).card * (((k+1:ℕ):ℝ))^n := hmul
      · -- case (ii): a subspace with many internal lines
        set A : Finset (Fin m → Fin (k+1)) := dktPull W T with hAdef
        have hAno : ¬ ∃ l : Line (Fin (k+1)) (Fin m), ∀ v, l v ∈ A := by
          rw [hAdef]; exact dkt_not_line_pull W T hline
        have hA2 : (ρ - 2*η) * (((k+1:ℕ):ℝ))^m ≤ (A.card : ℝ) := by
          rw [hAdef]; simp only [dktPull]; exact hW1
        have hcase : (ρ + η^2/2) * (((k+1:ℕ):ℝ))^m ≤ (A.card : ℝ) ∨
            (θ/2) * ((((k+1:ℕ):ℝ)^m) - ((k:ℝ)^m)) ≤
              (((varWord k m).filter (fun g => ∀ v : Fin k, linePt g v ∈ A)).card : ℝ) := by
          refine Or.inr ?_
          have heq : (varWord k m).filter (fun g => ∀ v : Fin k, linePt g v ∈ A)
              = (varWord k m).filter (fun g => ∀ v : Fin k, W (linePt g v) ∈ T) := by
            rw [hAdef]
            apply Finset.filter_congr
            intro g _
            simp only [mem_dktPull]
          rw [heq]; exact hW2
        obtain ⟨D, ⟨Ds, hinsens, hDdef⟩, hDcard, hDcorr⟩ :=
          dkt_insens_correlation k hk2 ρ θ η γ hρpos hρ1 hθpos hθ1 hηdef hγdef m hm1
            hm_lam_η A hA2 hAno hcase
        have hdensD : 2 * ((k:ℝ)) * β₀ * (((k+1:ℕ):ℝ))^m ≤ (D.card : ℝ) := by
          have h1 : (2 * ((k:ℝ)) * β₀) * (((k+1:ℕ):ℝ))^m = γ₀^2/2 * (((k+1:ℕ):ℝ))^m := by
            rw [htwo]
          rw [h1]
          have hstep : γ₀ * (((k+1:ℕ):ℝ)^m) ≤ γ * (((k+1:ℕ):ℝ)^m) :=
            mul_le_mul_of_nonneg_right hγ_ge (by positivity)
          linarith [hDcard, hdensD_ge, hstep]
        obtain ⟨VS, hVS_sub, hVS_disj, hVS_cov0⟩ := htil0 m hm_Ntil Ds hinsens D hDdef hdensD
        have hcov' : (D.card : ℝ) - γ^2/2 * (((k+1:ℕ):ℝ)^m) ≤
            ((VS.biUnion (fun S => Finset.univ.image (fun x => S x))).card : ℝ) := by
          have hγ2 : 2 * ((k:ℝ)) * β₀ ≤ γ^2/2 := by
            rw [htwo]; nlinarith [hγ_ge, hγpos]
          have hstep : 2 * ((k:ℝ)) * β₀ * (((k+1:ℕ):ℝ)^m) ≤ γ^2/2 * (((k+1:ℕ):ℝ)^m) :=
            mul_le_mul_of_nonneg_right hγ2 (by positivity)
          linarith [hVS_cov0, hstep]
        obtain ⟨V, hVmem, hVcard⟩ :=
          dktFinalStep (k := k) (d := d0) (m := m) (by omega) hγpos (by positivity)
            A D VS hDcard hDcorr hVS_sub hVS_disj hcov'
        refine ⟨scomp W V, ?_⟩
        rw [dkt_card_filter_scomp]
        have hVc := hVcard
        rw [dkt_inter_image_eq V A, Finset.card_image_of_injective _ (dkt_subspace_injective V)] at hVc
        rw [hAdef] at hVc
        have hVc' : (ρ + γ/2) * (((k+1:ℕ):ℝ)^d0)
            ≤ ((Finset.univ : Finset (Fin d0 → Fin (k+1))).filter
                (fun x => V x ∈ dktPull W T)).card := hVc
        have hmul := mul_le_mul_of_nonneg_right hVc' (le_of_lt hqn)
        have hLHS : (ρ + γ/2) * (((k+1:ℕ):ℝ)^d0) * (((k+1:ℕ):ℝ))^n
            = (T.card : ℝ) * (((k+1:ℕ):ℝ)^d0) + (γ/2) * (((k+1:ℕ):ℝ)^(n+d0)) := by
          have hρn : ρ * (((k+1:ℕ):ℝ))^n = (T.card : ℝ) := by
            rw [hρdef, div_mul_cancel₀ _ (ne_of_gt hqn)]
          have e : (((k+1:ℕ):ℝ))^d0 * (((k+1:ℕ):ℝ))^n = (((k+1:ℕ):ℝ))^(n+d0) := by
            rw [mul_comm, ← pow_add]
          calc (ρ + γ/2) * (((k+1:ℕ):ℝ)^d0) * (((k+1:ℕ):ℝ))^n
              = (ρ * (((k+1:ℕ):ℝ))^n) * (((k+1:ℕ):ℝ)^d0)
                  + (γ/2) * ((((k+1:ℕ):ℝ)^d0) * (((k+1:ℕ):ℝ))^n) := by ring
            _ = (T.card : ℝ) * (((k+1:ℕ):ℝ)^d0) + (γ/2) * (((k+1:ℕ):ℝ)^(n+d0)) := by
                  rw [hρn, e]
        have hge : γ₀/2 ≤ γ/2 := by linarith [hγ_ge]
        calc (T.card : ℝ) * (((k+1:ℕ):ℝ)^d0) + (γ₀/2) * (((k+1:ℕ):ℝ)^(n+d0))
            ≤ (T.card : ℝ) * (((k+1:ℕ):ℝ)^d0) + (γ/2) * (((k+1:ℕ):ℝ)^(n+d0)) := by
              have := mul_le_mul_of_nonneg_right hge (by positivity : (0:ℝ) ≤ (((k+1:ℕ):ℝ)^(n+d0)))
              linarith
          _ = (ρ + γ/2) * (((k+1:ℕ):ℝ)^d0) * (((k+1:ℕ):ℝ))^n := hLHS.symm
          _ ≤ ((Finset.univ : Finset (Fin d0 → Fin (k+1))).filter
                  (fun x => V x ∈ dktPull W T)).card * (((k+1:ℕ):ℝ))^n := hmul

end

end Commons.Combinatorics.Ramsey
