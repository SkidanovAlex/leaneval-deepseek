/-
# `nDist` and the `k`-fold sumset: the general facts

Two general facts about the distance-to-`ℤ` function `nDist` (`Work.KMTAreas.A4.denseMultiples_defs`)
and the `k`-fold sumset `kSum` (`Work.KMTAreas.A4.kSumDefs`):

* `nDist` is subadditive (it is the metric on `ℝ/ℤ`);
* consequently, if every element of `T ⊆ [-N,N]` is within `δ` of an integer, then every element
  of the `k`-fold sumset `kSum T k` is within `kδ` of an integer (`kSum_nDist_le`), and this
  sumset is contained in `[-kN,kN]` (`kSum_subset_bounds`).

together with the Freiman sumset bound and its cast/density forms,
these are the structural inputs of the amplification step (`Work.KMTAreas.A4.lip2Amplify`);
they are stated here in general form so that later arithmetic steps can import them instead of
re-deriving them.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.denseMultiples_defs
import Submission.Work.KMTAreas.A4.kSumDefs

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace Work.KMTAreas.A4

/-- `nDist` is subadditive: the distance to `ℤ` is the metric on the circle.

(Note: `Work.KMTAreas.A4.nDist_add_le` in `denseMultiples_K3.lean` is the same statement; this
name is used here so that the two modules can be imported together.) -/
theorem nDist_add_le' (x y : ℝ) : nDist (x + y) ≤ nDist x + nDist y := by
  have h1 : nDist (x + y) ≤ |x + y - ((round x + round y : ℤ) : ℝ)| :=
    nDist_le_abs_sub_int (x + y) (round x + round y)
  have h2 : x + y - ((round x + round y : ℤ) : ℝ) =
      (x - (round x : ℝ)) + (y - (round y : ℝ)) := by
    push_cast; ring
  rw [h2] at h1
  have h3 : |(x - (round x : ℝ)) + (y - (round y : ℝ))| ≤
      |x - (round x : ℝ)| + |y - (round y : ℝ)| := abs_add_le _ _
  simp only [nDist] at h1 h3 ⊢
  linarith

/-- The `k`-fold sumset of a set contained in `[-N,N]` is contained in `[-kN,kN]`. -/
theorem kSum_subset_bounds (N k : ℕ) (T : Finset ℤ)
    (hT : ∀ n ∈ T, -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ)) :
    ∀ a ∈ kSum T k, -(((k * N : ℕ)) : ℤ) ≤ a ∧ a ≤ (((k * N : ℕ)) : ℤ) := by
  induction k with
  | zero =>
      intro a ha
      rw [kSum_zero, Finset.mem_singleton] at ha
      subst ha
      norm_num
  | succ k ih =>
      intro a ha
      rw [kSum_succ, mem_addSet] at ha
      obtain ⟨t, ht, s, hs, hts⟩ := ha
      obtain ⟨hs1, hs2⟩ := ih s hs
      obtain ⟨ht1, ht2⟩ := hT t ht
      rw [← hts]
      have hcast : (((k + 1) * N : ℕ) : ℤ) = ((k * N : ℕ) : ℤ) + (N : ℤ) := by
        rw [Nat.cast_mul, Nat.cast_mul]
        push_cast
        ring
      rw [hcast]
      omega

/-- If every element of `T` is within `δ` of an integer, then every element of the `k`-fold
sumset of `T` is within `kδ` of an integer. -/
theorem kSum_nDist_le (k : ℕ) (T : Finset ℤ) (β δ : ℝ)
    (hgood : ∀ n ∈ T, nDist (β * (n : ℝ)) ≤ δ) :
    ∀ a ∈ kSum T k, nDist (β * (a : ℝ)) ≤ (k : ℝ) * δ := by
  induction k with
  | zero =>
      intro a ha
      rw [kSum_zero, Finset.mem_singleton] at ha
      subst ha
      simp [nDist]
  | succ k ih =>
      intro a ha
      rw [kSum_succ, mem_addSet] at ha
      obtain ⟨t, ht, s, hs, hts⟩ := ha
      have hs' := ih s hs
      have ht' := hgood t ht
      rw [← hts]
      have hcast : (((t + s : ℤ)) : ℝ) = (t : ℝ) + (s : ℝ) := by push_cast; ring
      rw [hcast, mul_add]
      calc nDist (β * (t : ℝ) + β * (s : ℝ))
          ≤ nDist (β * (t : ℝ)) + nDist (β * (s : ℝ)) := nDist_add_le' _ _
        _ ≤ (k : ℝ) * δ + δ := by linarith [hs', ht']
        _ = ((k + 1 : ℕ) : ℝ) * δ := by push_cast; ring

/-- **Freiman's two-set sumset bound in `ℤ`**: for nonempty finite `A B ⊆ ℤ`,
`|A| + |B| ≤ |A + B| + 1`, i.e. `|A + B| ≥ |A| + |B| - 1`.

Proof: with `a₀ = min A`, `b₀ = max B`, the two sets `A + b₀` and `a₀ + B` have `|A|` and `|B|`
elements, lie in `addSet A B`, and meet only in `a₀ + b₀` (an `x` in both is `a + b₀ = a₀ + b`
with `a ≥ a₀`, `b ≤ b₀`, forcing `a = a₀`, `b = b₀`).  Hence
`|A| + |B| = |(A + b₀) ∪ (a₀ + B)| + 1 ≤ |addSet A B| + 1`. -/
theorem addSet_card_bound (A B : Finset ℤ) (hA : A.Nonempty) (hB : B.Nonempty) :
    A.card + B.card ≤ (addSet A B).card + 1 := by
  set a₀ := A.min' hA with ha₀
  set b₀ := B.max' hB with hb₀
  have ha₀A : a₀ ∈ A := A.min'_mem hA
  have hb₀B : b₀ ∈ B := B.max'_mem hB
  have hsub : A.image (fun a => a + b₀) ∪ B.image (fun b => a₀ + b) ⊆ addSet A B := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
      exact mem_addSet.mpr ⟨a, ha, b₀, hb₀B, rfl⟩
    · rcases Finset.mem_image.mp hx with ⟨b, hb, rfl⟩
      exact mem_addSet.mpr ⟨a₀, ha₀A, b, hb, rfl⟩
  have hcard1 : (A.image (fun a => a + b₀)).card = A.card :=
    Finset.card_image_of_injective _ (fun x y h => by omega)
  have hcard2 : (B.image (fun b => a₀ + b)).card = B.card :=
    Finset.card_image_of_injective _ (fun x y h => by omega)
  have hinter : (A.image (fun a => a + b₀) ∩ B.image (fun b => a₀ + b)).card ≤ 1 := by
    have hle : A.image (fun a => a + b₀) ∩ B.image (fun b => a₀ + b) ⊆ {a₀ + b₀} := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
      obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hx1
      obtain ⟨b, hb, hbx⟩ := Finset.mem_image.mp hx2
      have ha₀le : a₀ ≤ a := ha₀.le.trans (A.min'_le a ha)
      have hble : b ≤ b₀ := (B.le_max' b hb).trans hb₀.le
      have haea : a = a₀ := by omega
      have hbeb : b = b₀ := by omega
      rw [Finset.mem_singleton]
      omega
    calc (A.image (fun a => a + b₀) ∩ B.image (fun b => a₀ + b)).card
        ≤ ({a₀ + b₀} : Finset ℤ).card := Finset.card_le_card hle
      _ = 1 := Finset.card_singleton _
  have hunion := Finset.card_union_add_card_inter (A.image (fun a => a + b₀))
    (B.image (fun b => a₀ + b))
  have hle2 := Finset.card_le_card hsub
  omega

/-- **The `k`-fold sumset keeps at least `k(|T| - 1) + 1` elements** (Freiman's bound iterated),
in the real-valued (`cast`) form in which the amplification consumes it. -/
theorem kSum_card_le_cast (T : Finset ℤ) (hT : T.Nonempty) (k : ℕ) :
    (k : ℝ) * (T.card : ℝ) ≤ ((kSum T k).card : ℝ) + ((k : ℝ) - 1) := by
  induction k with
  | zero => simp
  | succ n ih =>
      have hne := kSum_nonempty T hT n
      have hfr := addSet_card_bound T (kSum T n) hT hne
      have hfrR : (T.card : ℝ) + ((kSum T n).card : ℝ)
          ≤ ((addSet T (kSum T n)).card : ℝ) + 1 := by exact_mod_cast hfr
      rw [kSum_succ]
      push_cast
      linarith [ih, hfrR]

/-- **The density bookkeeping of the amplification step.**  If `T ⊆ [-N,N]` is `δ₂`-dense
(`δ₂(2N+1) ≤ |T|`, `δ₂ ≤ 1`, `1 ≤ δ₂(N+1)`) then its `k`-fold sumset (`k ≥ 1`) is `δ₂/4`-dense
in the enlarged interval `[-kN,kN]`: `(δ₂/4)(2kN+1) ≤ |kSum T k|`.  This is where Freiman's bound
*preserves* the density (a Cauchy--Schwarz argument would lose a factor `δ₂`). -/
theorem kSum_card_dens (T : Finset ℤ) (hT : T.Nonempty) {k : ℕ} (hk : 1 ≤ k)
    {δ₂ : ℝ} (hδ₂ : 0 < δ₂) (hδ₂1 : δ₂ ≤ 1) {N : ℕ}
    (hdens : 1 ≤ δ₂ * ((N : ℝ) + 1))
    (hcard : δ₂ * (2 * (N : ℝ) + 1) ≤ (T.card : ℝ)) :
    (δ₂ / 4) * (2 * ((k * N : ℕ) : ℝ) + 1) ≤ ((kSum T k).card : ℝ) := by
  have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hclR := kSum_card_le_cast T hT k
  have hmul : (k : ℝ) * (δ₂ * (2 * (N : ℝ) + 1)) ≤ (k : ℝ) * (T.card : ℝ) :=
    mul_le_mul_of_nonneg_left hcard (by linarith : (0 : ℝ) ≤ (k : ℝ))
  have hstep : (k : ℝ) * δ₂ * (2 * (N : ℝ) + 1) - ((k : ℝ) - 1) ≤ ((kSum T k).card : ℝ) := by
    linarith [hclR, hmul]
  have hkC : (δ₂ / 4) * (2 * (k : ℝ) * (N : ℝ) + 1)
      ≤ (k : ℝ) * δ₂ * (2 * (N : ℝ) + 1) - ((k : ℝ) - 1) := by
    have hNδ : 1 - δ₂ ≤ (N : ℝ) * δ₂ := by nlinarith [hdens]
    nlinarith [hNδ, hk1R, hδ₂1, hδ₂]
  have hkn : (2 * ((k * N : ℕ) : ℝ) + 1) = 2 * (k : ℝ) * (N : ℝ) + 1 := by
    rw [Nat.cast_mul]; ring
  rw [hkn]
  linarith [hkC, hstep]

end Work.KMTAreas.A4
