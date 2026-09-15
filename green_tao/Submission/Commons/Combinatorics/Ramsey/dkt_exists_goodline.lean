import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Int.Star
import Submission.Commons.Combinatorics.Ramsey.mdhj_of_dhj
import Submission.Commons.Combinatorics.Ramsey.kvec_injective
import Submission.Commons.Combinatorics.Ramsey.card_varWord

open Finset
open _root_.Combinatorics

namespace Commons.Combinatorics.Ramsey

noncomputable section

/-- Embed `[k]^{m₀}` into `[k]^m` by placing the letters in the first `m₀` coordinates. -/
def glIota (m₀ m k : ℕ) [NeZero k] (z : Fin m₀ → Fin k) : Fin m → Fin k :=
  fun i => if h : (i : ℕ) < m₀ then z ⟨i, h⟩ else 0

/-- Lift a line index word of `[k]^{m₀}` to a line index word of `[k]^m` (first `m₀` coordinates). -/
def glSigma (m₀ m k : ℕ) [NeZero k] (g : Fin m₀ → Option (Fin k)) : Fin m → Option (Fin k) :=
  fun i => if h : (i : ℕ) < m₀ then g ⟨i, h⟩ else some 0

/-- The index word in `[k]^M` of the substitution of `σ` into the subspace `S`. -/
def glSubst {k m M : ℕ} (S : Subspace (Fin m) (Fin k) (Fin M)) (σ : Fin m → Option (Fin k)) :
    Fin M → Option (Fin k) :=
  fun i => (S.idxFun i).elim (fun a => some a) σ

lemma glSigma_apply_of_lt {m₀ m k : ℕ} [NeZero k] (g : Fin m₀ → Option (Fin k)) {i : Fin m}
    (h : (i : ℕ) < m₀) : glSigma m₀ m k g i = g ⟨i, h⟩ := dif_pos h

lemma glSigma_apply_of_ge {m₀ m k : ℕ} [NeZero k] (g : Fin m₀ → Option (Fin k)) {i : Fin m}
    (h : ¬ (i : ℕ) < m₀) : glSigma m₀ m k g i = some 0 := dif_neg h

lemma glIota_apply_of_lt {m₀ m k : ℕ} [NeZero k] (z : Fin m₀ → Fin k) {i : Fin m}
    (h : (i : ℕ) < m₀) : glIota m₀ m k z i = z ⟨i, h⟩ := dif_pos h

lemma glIota_apply_of_ge {m₀ m k : ℕ} [NeZero k] (z : Fin m₀ → Fin k) {i : Fin m}
    (h : ¬ (i : ℕ) < m₀) : glIota m₀ m k z i = 0 := dif_neg h

/-- The `v`-th point of the lifted line is the lift of the `v`-th point of the original line. -/
lemma glSigma_getD {m₀ m k : ℕ} [NeZero k] (g : Fin m₀ → Option (Fin k)) (v : Fin k) :
    (fun i => (glSigma m₀ m k g i).getD v) = glIota m₀ m k (fun j => (g j).getD v) := by
  funext i
  by_cases h : (i : ℕ) < m₀
  · rw [glSigma_apply_of_lt g h, glIota_apply_of_lt _ h]
  · rw [glSigma_apply_of_ge g h, glIota_apply_of_ge _ h]
    rfl

/-- The lifted line of a combinatorial line, as a function on the alphabet. -/
lemma glSigma_line {m₀ m k : ℕ} [NeZero k] (l : Line (Fin k) (Fin m₀)) (v : Fin k) :
    (fun i => (glSigma m₀ m k l.idxFun i).getD v) = glIota m₀ m k (l v) := by
  rw [glSigma_getD]
  exact congrArg (glIota m₀ m k) (Line.apply_def l v).symm

lemma glSigma_hasWild {m₀ m k : ℕ} [NeZero k] (hm : m₀ ≤ m) (g : Fin m₀ → Option (Fin k))
    (hg : ∃ j, g j = none) : ∃ i : Fin m, glSigma m₀ m k g i = none := by
  obtain ⟨j, hj⟩ := hg
  refine ⟨⟨(j : ℕ), by omega⟩, ?_⟩
  rw [glSigma_apply_of_lt g (by simpa using j.isLt)]
  exact hj

lemma glSubst_hasWild {k m M : ℕ} (S : Subspace (Fin m) (Fin k) (Fin M))
    (σ : Fin m → Option (Fin k)) (hσ : ∃ e, σ e = none) : ∃ i, glSubst S σ i = none := by
  obtain ⟨e, he⟩ := hσ
  obtain ⟨i, hi⟩ := S.proper e
  exact ⟨i, by rw [glSubst, hi, Sum.elim_inr, he]⟩

/-- The points of the line prescribed by `glSubst S σ` are the points of the line prescribed
by `σ`, pushed forward by the subspace `S`. -/
lemma linePt_glSubst {k m M : ℕ} (S : Subspace (Fin m) (Fin k) (Fin M))
    (σ : Fin m → Option (Fin k)) (v : Fin k) :
    linePt (glSubst S σ) v = kvec (S (fun i => (σ i).getD v)) := by
  funext j
  rw [linePt, glSubst, kvec, Subspace.coe_apply]
  cases h : S.idxFun j with
  | inl a => simp
  | inr e => simp

/-- Cardinality of a filter as a sum of indicators, in `ℝ`. -/
lemma cast_card_filter_univ {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (((Finset.univ : Finset α).filter p).card : ℝ)
      = ∑ a : α, (if p a then (1 : ℝ) else 0) := by
  rw [Finset.card_filter]
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases h : p a <;> simp [h]

theorem dkt_exists_goodline (k m m₀ M l n : ℕ) (hk : 2 ≤ k) (hm₀ : 1 ≤ m₀) (hm : m₀ ≤ m)
    (δ θ η : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hη : η = δ * θ / 48)
    (hdhj₀ : ∀ n' : ℕ, m₀ ≤ n' → ∀ T : Finset (Fin n' → Fin k),
      (δ / 4) * (k : ℝ) ^ n' ≤ (T.card : ℝ) →
        ∃ l' : _root_.Combinatorics.Line (Fin k) (Fin n'), ∀ x : Fin k, l' x ∈ T)
    (hθm : θ * (((k+1 : ℕ) : ℝ) ^ m₀ - (k : ℝ) ^ m₀) ≤ δ / 4)
    (S : _root_.Combinatorics.Subspace (Fin m) (Fin k) (Fin M))
    (V : _root_.Combinatorics.Subspace (Fin M) (Fin (k+1)) (Fin l)) (hl : l < n)
    (A : Finset (Fin n → Fin (k+1)))
    (hV : ∀ x : Fin M → Fin (k+1),
      (δ - η^2/2) * (((k+1 : ℕ) : ℝ) ^ (n - l)) ≤
        (((Finset.univ : Finset (Fin (n-l) → Fin (k+1))).filter
          (fun y => Commons.Combinatorics.Ramsey.cat (le_of_lt hl) (V x) y ∈ A)).card : ℝ)) :
    ∃ σ : Fin m → Option (Fin k), (∃ e, σ e = none) ∧
      θ * (((k+1 : ℕ) : ℝ) ^ (n - l)) ≤
        (((Finset.univ : Finset (Fin (n-l) → Fin (k+1))).filter
          (fun y => ∀ v : Fin k, Commons.Combinatorics.Ramsey.cat (le_of_lt hl)
            (V (Commons.Combinatorics.Ramsey.linePt
              (fun i => (S.idxFun i).elim (fun a => some a) σ) v)) y ∈ A)).card : ℝ) := by
  classical
  haveI : NeZero k := ⟨by omega⟩
  have hl' : l ≤ n := le_of_lt hl
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk1pos : (0 : ℝ) < ((k+1 : ℕ) : ℝ) := by positivity
  have hPpos : (0 : ℝ) < (((k+1 : ℕ) : ℝ) ^ (n - l)) := pow_pos hk1pos _
  have hηpos : 0 < η := by rw [hη]; positivity
  have hηle : η ≤ δ := by rw [hη]; nlinarith [hδ, hθ, hθ1]
  have hη2 : η^2 ≤ δ := by nlinarith [hηpos, hηle, hδ1, sq_nonneg (η - 1)]
  -- the slices and the `y`-level sets
  let Ax : (Fin M → Fin (k+1)) → Finset (Fin (n-l) → Fin (k+1)) :=
    fun x => (Finset.univ : Finset (Fin (n-l) → Fin (k+1))).filter
      (fun y => cat hl' (V x) y ∈ A)
  let Tl : (Fin (n-l) → Fin (k+1)) → Finset (Fin m₀ → Fin k) :=
    fun y => (Finset.univ : Finset (Fin m₀ → Fin k)).filter
      (fun z => cat hl' (V (kvec (S (glIota m₀ m k z)))) y ∈ A)
  have hAx : ∀ z : Fin m₀ → Fin k,
      (δ - η^2/2) * (((k+1 : ℕ) : ℝ) ^ (n - l))
        ≤ ((Ax (kvec (S (glIota m₀ m k z)))).card : ℝ) := fun z => hV _
  have hcardU : ((Finset.univ : Finset (Fin m₀ → Fin k)).card : ℝ) = (k : ℝ)^m₀ := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow]
  have hcardTl : ∀ y, ((Tl y).card : ℝ) ≤ (k : ℝ)^m₀ := by
    intro y
    have h : (Tl y).card ≤ (Finset.univ : Finset (Fin m₀ → Fin k)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h
    calc ((Tl y).card : ℝ) ≤ ((k^m₀ : ℕ) : ℝ) := by exact_mod_cast h
      _ = (k : ℝ)^m₀ := by rw [Nat.cast_pow]
  -- double counting
  have hdouble : ∑ z : Fin m₀ → Fin k, ((Ax (kvec (S (glIota m₀ m k z)))).card : ℝ)
      = ∑ y : Fin (n-l) → Fin (k+1), ((Tl y).card : ℝ) := by
    have e1 : ∀ z : Fin m₀ → Fin k, ((Ax (kvec (S (glIota m₀ m k z)))).card : ℝ)
        = ∑ y : Fin (n-l) → Fin (k+1),
            (if cat hl' (V (kvec (S (glIota m₀ m k z)))) y ∈ A then (1 : ℝ) else 0) := by
      intro z; exact cast_card_filter_univ _
    have e2 : ∀ y : Fin (n-l) → Fin (k+1), ((Tl y).card : ℝ)
        = ∑ z : Fin m₀ → Fin k,
            (if cat hl' (V (kvec (S (glIota m₀ m k z)))) y ∈ A then (1 : ℝ) else 0) := by
      intro y; exact cast_card_filter_univ _
    simp only [e1, e2]
    exact Finset.sum_comm
  have hlower : (k : ℝ)^m₀ * ((δ - η^2/2) * (((k+1 : ℕ) : ℝ) ^ (n - l)))
      ≤ ∑ z : Fin m₀ → Fin k, ((Ax (kvec (S (glIota m₀ m k z)))).card : ℝ) := by
    have hconst : ∑ _z : Fin m₀ → Fin k, ((δ - η^2/2) * (((k+1 : ℕ) : ℝ) ^ (n - l)))
        = (k : ℝ)^m₀ * ((δ - η^2/2) * (((k+1 : ℕ) : ℝ) ^ (n - l))) := by
      rw [Finset.sum_const, nsmul_eq_mul, hcardU]
    rw [← hconst]
    exact Finset.sum_le_sum (fun z _ => hAx z)
  -- the good set of `y`
  let thr : ℝ := (δ/4) * (k : ℝ)^m₀
  let G : Finset (Fin (n-l) → Fin (k+1)) :=
    (Finset.univ : Finset (Fin (n-l) → Fin (k+1))).filter (fun y => thr ≤ ((Tl y).card : ℝ))
  let Gc : Finset (Fin (n-l) → Fin (k+1)) :=
    (Finset.univ : Finset (Fin (n-l) → Fin (k+1))).filter (fun y => ¬ thr ≤ ((Tl y).card : ℝ))
  have hGcard : G.card + Gc.card = (k+1)^(n-l) := by
    dsimp only [G, Gc]
    rw [Finset.card_filter_add_card_filter_not]
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have hsplit : G.sum (fun y => ((Tl y).card : ℝ)) + Gc.sum (fun y => ((Tl y).card : ℝ))
      = ∑ y : Fin (n-l) → Fin (k+1), ((Tl y).card : ℝ) := by
    dsimp only [G, Gc]
    rw [Finset.sum_filter_add_sum_filter_not]
  have hupper : ∑ y : Fin (n-l) → Fin (k+1), ((Tl y).card : ℝ)
      ≤ (G.card : ℝ) * (k : ℝ)^m₀ + (Gc.card : ℝ) * thr := by
    rw [← hsplit]
    apply add_le_add
    · calc G.sum (fun y => ((Tl y).card : ℝ)) ≤ G.sum (fun _ => (k : ℝ)^m₀) :=
            Finset.sum_le_sum (fun y _ => hcardTl y)
        _ = (G.card : ℝ) * (k : ℝ)^m₀ := by rw [Finset.sum_const, nsmul_eq_mul]
    · calc Gc.sum (fun y => ((Tl y).card : ℝ)) ≤ Gc.sum (fun _ => thr) := by
            refine Finset.sum_le_sum (fun y hy => le_of_lt ?_)
            exact not_le.mp (Finset.mem_filter.mp hy).2
        _ = (Gc.card : ℝ) * thr := by rw [Finset.sum_const, nsmul_eq_mul]
  have hGcR : (Gc.card : ℝ) = (((k+1 : ℕ) : ℝ) ^ (n - l)) - (G.card : ℝ) := by
    have hle : G.card ≤ (k+1)^(n-l) := by omega
    have hsub : Gc.card = (k+1)^(n-l) - G.card := by omega
    rw [hsub, Nat.cast_sub hle, Nat.cast_pow]
  have hKpos : (0 : ℝ) < (k : ℝ)^m₀ := pow_pos hkpos _
  have hmain : (δ - η^2/2) * (((k+1 : ℕ) : ℝ) ^ (n - l))
      ≤ (G.card : ℝ) + (δ/4) * ((((k+1 : ℕ) : ℝ) ^ (n - l)) - (G.card : ℝ)) := by
    have h2 : ∑ y : Fin (n-l) → Fin (k+1), ((Tl y).card : ℝ)
        ≤ (G.card : ℝ) * (k : ℝ)^m₀
          + ((((k+1 : ℕ) : ℝ) ^ (n - l)) - (G.card : ℝ)) * thr := by
      rw [hGcR] at hupper; exact hupper
    have h3 : (G.card : ℝ) * (k : ℝ)^m₀
          + ((((k+1 : ℕ) : ℝ) ^ (n - l)) - (G.card : ℝ)) * thr
        = (k : ℝ)^m₀ * ((G.card : ℝ)
          + (δ/4) * ((((k+1 : ℕ) : ℝ) ^ (n - l)) - (G.card : ℝ))) := by
      dsimp only [thr]; ring
    have h1 : (k : ℝ)^m₀ * ((δ - η^2/2) * (((k+1 : ℕ) : ℝ) ^ (n - l)))
        ≤ ∑ y : Fin (n-l) → Fin (k+1), ((Tl y).card : ℝ) :=
      le_trans hlower (le_of_eq hdouble)
    rw [h3] at h2
    exact (mul_le_mul_iff_of_pos_left hKpos).mp (le_trans h1 h2)
  have hG : (δ/4) * (((k+1 : ℕ) : ℝ) ^ (n - l)) ≤ (G.card : ℝ) := by
    have hδge : (δ/4) * (1 - δ/4) ≤ 3*δ/4 - η^2/2 := by nlinarith [hη2, hδ, hδ1]
    have h1 : ((3*δ/4 - η^2/2)) * (((k+1 : ℕ) : ℝ) ^ (n - l))
        ≤ (G.card : ℝ) * (1 - δ/4) := by nlinarith [hmain]
    have h2 : ((δ/4) * (1 - δ/4)) * (((k+1 : ℕ) : ℝ) ^ (n - l))
        ≤ (G.card : ℝ) * (1 - δ/4) := by nlinarith [h1, hδge, hPpos]
    have hδ4 : (0 : ℝ) < 1 - δ/4 := by linarith
    have h3 : ((δ/4) * (((k+1 : ℕ) : ℝ) ^ (n - l))) * (1 - δ/4)
        ≤ (G.card : ℝ) * (1 - δ/4) := by nlinarith [h2]
    exact (mul_le_mul_iff_of_pos_right hδ4).mp h3
  -- pigeonhole over lines
  have hDpos : 0 < (k+1)^m₀ - k^m₀ := by
    have hlt : k^m₀ < (k+1)^m₀ := Nat.pow_lt_pow_left (by omega) (by omega)
    omega
  have hgood : ∀ y : {y : Fin (n-l) → Fin (k+1) // y ∈ G},
      ∃ l : Line (Fin k) (Fin m₀), ∀ v : Fin k, l v ∈ Tl y.1 := by
    intro y
    have hy : (δ/4) * (k : ℝ)^m₀ ≤ ((Tl y.1).card : ℝ) := by
      have h := (Finset.mem_filter.mp y.2).2
      dsimp only [thr] at h
      exact h
    exact hdhj₀ m₀ le_rfl (Tl y.1) hy
  let f : {y : Fin (n-l) → Fin (k+1) // y ∈ G} → Line (Fin k) (Fin m₀) :=
    fun y => Classical.choose (hgood y)
  have hf_spec : ∀ (y : {y : Fin (n-l) → Fin (k+1) // y ∈ G}) (v : Fin k),
      f y v ∈ Tl y.1 := fun y v => Classical.choose_spec (hgood y) v
  have hD : (G.attach.image f).card ≤ (k+1)^m₀ - k^m₀ := by
    have h1 : (G.attach.image f).card ≤ (Finset.univ : Finset (Line (Fin k) (Fin m₀))).card :=
      Finset.card_le_card (Finset.subset_univ _)
    have h2 : (Finset.univ : Finset (Line (Fin k) (Fin m₀))).card ≤ (k+1)^m₀ - k^m₀ := by
      have h3 : (Finset.univ.image (fun l : Line (Fin k) (Fin m₀) => l.idxFun))
          ⊆ varWord k m₀ := by
        intro g hg
        rw [Finset.mem_image] at hg
        obtain ⟨l, -, rfl⟩ := hg
        rw [mem_varWord]
        exact l.proper
      calc (Finset.univ : Finset (Line (Fin k) (Fin m₀))).card
          = (Finset.univ.image (fun l : Line (Fin k) (Fin m₀) => l.idxFun)).card := by
            rw [Finset.card_image_of_injective _ (fun l m h => Line.ext h)]
        _ ≤ (varWord k m₀).card := Finset.card_le_card h3
        _ = (k+1)^m₀ - k^m₀ := card_varWord k m₀
    linarith
  have hcGpos : 0 < (δ/4) * (((k+1 : ℕ) : ℝ) ^ (n - l)) := by positivity
  obtain ⟨l₀, hl₀⟩ := exists_card_fiber_ge_div (s := G.attach) (f := f)
    ((δ/4) * (((k+1 : ℕ) : ℝ) ^ (n - l))) ((k+1)^m₀ - k^m₀)
    hcGpos hDpos hD (by rw [Finset.card_attach]; exact hG)
  -- compare with `θ * (k+1)^(n-l)`
  have hθN : θ * (((k+1 : ℕ) : ℝ) ^ (n - l))
      ≤ (δ/4) * (((k+1 : ℕ) : ℝ) ^ (n - l)) / (((k+1)^m₀ - k^m₀ : ℕ) : ℝ) := by
    have hL : (((k+1)^m₀ - k^m₀ : ℕ) : ℝ) = ((k+1 : ℕ) : ℝ)^m₀ - (k : ℝ)^m₀ := by
      rw [Nat.cast_sub (le_of_lt (by
        have hlt : k^m₀ < (k+1)^m₀ := Nat.pow_lt_pow_left (by omega) (by omega)
        omega)), Nat.cast_pow, Nat.cast_pow]
    have hLpos : (0 : ℝ) < (((k+1)^m₀ - k^m₀ : ℕ) : ℝ) := by exact_mod_cast hDpos
    have hθm' : θ * (((k+1 : ℕ) : ℝ)^m₀ - (k : ℝ)^m₀) ≤ δ/4 := hθm
    have hstep : θ * (((k+1 : ℕ) : ℝ)^m₀ - (k : ℝ)^m₀) * (((k+1 : ℕ) : ℝ) ^ (n-l))
        ≤ (δ/4) * (((k+1 : ℕ) : ℝ) ^ (n - l)) :=
      mul_le_mul_of_nonneg_right hθm' (le_of_lt hPpos)
    rw [← hL] at hstep
    rw [le_div_iff₀ hLpos]
    calc θ * (((k+1 : ℕ) : ℝ) ^ (n - l)) * (((k+1)^m₀ - k^m₀ : ℕ) : ℝ)
        = θ * ((((k+1)^m₀ - k^m₀ : ℕ) : ℝ)) * (((k+1 : ℕ) : ℝ) ^ (n - l)) := by ring
      _ ≤ (δ/4) * (((k+1 : ℕ) : ℝ) ^ (n - l)) := hstep
  -- the final set
  let Y : Finset (Fin (n-l) → Fin (k+1)) :=
    (Finset.univ : Finset (Fin (n-l) → Fin (k+1))).filter
      (fun y => ∀ v : Fin k, cat hl' (V (linePt (glSubst S (glSigma m₀ m k l₀.idxFun)) v)) y ∈ A)
  have hYle : ((G.attach.filter (fun y => f y = l₀)).card : ℝ) ≤ (Y.card : ℝ) := by
    have hmap : Set.MapsTo (fun y : {y : Fin (n-l) → Fin (k+1) // y ∈ G} => y.1)
        ↑(G.attach.filter (fun y => f y = l₀)) ↑Y := by
      intro y hy
      rw [Finset.mem_coe, Finset.mem_filter] at hy
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro v
      have hmem : l₀ v ∈ Tl y.1 := by rw [← hy.2]; exact hf_spec y v
      rw [Finset.mem_filter] at hmem
      simpa only [linePt_glSubst S (glSigma m₀ m k l₀.idxFun) v, glSigma_line l₀ v] using hmem.2
    calc ((G.attach.filter (fun y => f y = l₀)).card : ℝ)
        = (((G.attach.filter (fun y => f y = l₀)).image (fun y => y.1)).card : ℝ) := by
          rw [Finset.card_image_of_injective _ Subtype.val_injective]
      _ ≤ (Y.card : ℝ) := by
          exact_mod_cast Finset.card_le_card (Finset.image_subset_iff.mpr hmap)
  refine ⟨glSigma m₀ m k l₀.idxFun, glSigma_hasWild hm l₀.idxFun l₀.proper, ?_⟩
  show θ * (((k+1 : ℕ) : ℝ) ^ (n - l)) ≤ (Y.card : ℝ)
  linarith [hl₀, hθN, hYle]

end

end Commons.Combinatorics.Ramsey