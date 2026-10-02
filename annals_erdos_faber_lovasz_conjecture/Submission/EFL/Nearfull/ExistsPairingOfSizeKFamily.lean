import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith.Frontend
import Submission.Commons.Data.Finset.sum_card_filter_comm
import Submission.EFL.Nearfull.ExistsUsefulPairsInClique
import Submission.Commons.Combinatorics.Hypergraph.pairing_of_useful_pairs

set_option maxHeartbeats 1000000

namespace Commons.Combinatorics.Hypergraph

/-! ## Helper lemmas -/

/-- **Degree bound for a linear hypergraph of `k`-sets.**  If `A` is a finite family of
`k`-subsets of `Fin n` that pairwise intersect in at most one point, then at most
`(n-1)/(k-1)` members of `A` contain any fixed point `x`. -/
private theorem ncard_le_div {n k : ℕ} (A : Finset (Set (Fin n)))
    (hsize : ∀ e ∈ A, e.ncard = k)
    (hlin : ∀ e ∈ A, ∀ f ∈ A, e ≠ f → (e ∩ f).Subsingleton)
    (hk : 2 ≤ k) (x : Fin n) :
    Set.ncard {e : Set (Fin n) | e ∈ (A : Set (Set (Fin n))) ∧ x ∈ e} ≤ (n - 1) / (k - 1) := by
  classical
  have hset : {e : Set (Fin n) | e ∈ (A : Set (Set (Fin n))) ∧ x ∈ e}
      = (↑(A.filter (fun e => x ∈ e)) : Set (Set (Fin n))) := by
    ext e; simp
  rw [hset, Set.ncard_coe_finset]
  set A' : Finset (Set (Fin n)) := A.filter (fun e => x ∈ e) with hA'def
  have hmemA' : ∀ e ∈ A', e ∈ A ∧ x ∈ e := by
    intro e he
    rw [hA'def] at he
    exact Finset.mem_filter.mp he
  set s : Set (Fin n) → Finset (Fin n) := fun e => e.toFinite.toFinset.erase x with hs
  have hs_coe : ∀ e, (s e : Set (Fin n)) = e \ {x} := by
    intro e; rw [hs]; simp [Finset.coe_erase]
  have hs_card : ∀ e ∈ A', (s e).card = k - 1 := by
    intro e he
    obtain ⟨heA, hxe⟩ := hmemA' e he
    rw [← Set.ncard_coe_finset (s e), hs_coe e]
    rw [Set.ncard_sdiff_singleton_of_mem hxe, hsize e heA]
  have hdisj : (↑A' : Set (Set (Fin n))).PairwiseDisjoint s := by
    intro e he f hf hef
    apply Finset.disjoint_left.mpr
    intro y hye hyf
    have heA : e ∈ A := (hmemA' e he).1
    have hfA : f ∈ A := (hmemA' f hf).1
    have hxe : x ∈ e := (hmemA' e he).2
    have hxf : x ∈ f := (hmemA' f hf).2
    have hsub : (e ∩ f).Subsingleton := hlin e heA f hfA hef
    have heq : e ∩ f = {x} := hsub.eq_singleton_of_mem ⟨hxe, hxf⟩
    have hyeS : y ∈ (s e : Set (Fin n)) := by simpa using hye
    rw [hs_coe e] at hyeS
    have hyfS : y ∈ (s f : Set (Fin n)) := by simpa using hyf
    rw [hs_coe f] at hyfS
    have hye' : y ∈ e := hyeS.1
    have hyx : y ≠ x := by simpa using hyeS.2
    have hyf' : y ∈ f := hyfS.1
    exact hyx (by have h : y ∈ e ∩ f := ⟨hye', hyf'⟩; rw [heq] at h; simpa using h)
  have hbU : (A'.biUnion s).card = A'.card * (k - 1) := by
    rw [Finset.card_biUnion hdisj]
    rw [Finset.sum_congr rfl (fun e he => hs_card e he)]
    rw [Finset.sum_const, smul_eq_mul]
  have hsub : A'.biUnion s ⊆ (Finset.univ : Finset (Fin n)).erase x := by
    intro y hy
    rw [Finset.mem_biUnion] at hy
    obtain ⟨e, he, hye⟩ := hy
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ y⟩
    rw [hs] at hye
    exact (Finset.mem_erase.mp hye).1
  change A'.card ≤ (n - 1) / (k - 1)
  rw [Nat.le_div_iff_mul_le (by omega : 0 < k - 1)]
  calc A'.card * (k - 1) = (A'.biUnion s).card := hbU.symm
    _ ≤ ((Finset.univ : Finset (Fin n)).erase x).card := Finset.card_le_card hsub
    _ = n - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, Fintype.card_fin]

/-- The degree bound in the real form `2√n`, assuming `k - 1 ≥ √n/2`. -/
private theorem ncard_le_two_sqrt {n k : ℕ} (A : Finset (Set (Fin n)))
    (hsize : ∀ e ∈ A, e.ncard = k)
    (hlin : ∀ e ∈ A, ∀ f ∈ A, e ≠ f → (e ∩ f).Subsingleton)
    (hk : 2 ≤ k) (hn1 : 1 ≤ n) (hkn : Real.sqrt n / 2 ≤ (k : ℝ) - 1) (x : Fin n) :
    (Set.ncard {e : Set (Fin n) | e ∈ (A : Set (Set (Fin n))) ∧ x ∈ e} : ℝ)
      ≤ 2 * Real.sqrt n := by
  have hdiv := ncard_le_div A hsize hlin hk x
  set N : ℕ := Set.ncard {e : Set (Fin n) | e ∈ (A : Set (Set (Fin n))) ∧ x ∈ e} with hN
  have hdiv' : N ≤ (n - 1) / (k - 1) := hdiv
  have hk1 : (1 : ℕ) ≤ k := by omega
  have hmul : N * (k - 1) ≤ n - 1 := by
    calc N * (k - 1) ≤ ((n - 1) / (k - 1)) * (k - 1) := Nat.mul_le_mul_right _ hdiv'
      _ ≤ n - 1 := Nat.div_mul_le_self _ _
  have hcast : (N : ℝ) * ((k : ℝ) - 1) ≤ (n : ℝ) - 1 := by
    have h : ((N * (k - 1) : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hmul
    rw [Nat.cast_mul, Nat.cast_sub hk1, Nat.cast_sub hn1] at h
    push_cast at h
    linarith [h]
  have hk1pos : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hNle : (N : ℝ) ≤ ((n : ℝ) - 1) / ((k : ℝ) - 1) := by
    rw [le_div_iff₀ hk1pos]; exact hcast
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hspos : 0 < Real.sqrt n := by
    have := Real.one_le_sqrt.mpr hnR
    linarith
  have hnum_nonneg : 0 ≤ (n : ℝ) - 1 := by linarith
  have hfrac : ((n : ℝ) - 1) / ((k : ℝ) - 1) ≤ ((n : ℝ) - 1) / (Real.sqrt n / 2) :=
    div_le_div_of_nonneg_left hnum_nonneg (by linarith) hkn
  have h2 : ((n : ℝ) - 1) / (Real.sqrt n / 2) ≤ 2 * Real.sqrt n := by
    rw [div_le_iff₀ (by linarith : 0 < Real.sqrt n / 2)]
    have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := by rw [← sq, Real.sq_sqrt (by linarith)]
    nlinarith [hsq, Real.sqrt_nonneg n]
  have : (N : ℝ) ≤ ((n : ℝ) - 1) / (Real.sqrt n / 2) := le_trans hNle hfrac
  linarith [this, h2]

/-- The two ways of saying that a hyperedge meets both `e` and `f` describe subtypes
with the same cardinality. -/
private lemma useful_card_eq {n : ℕ} (𝓗 : Set (Set (Fin n)))
    (e f : {e : Set (Fin n) // e ∈ 𝓗}) :
    Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} // g ≠ e ∧ g ≠ f ∧
        ((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty ∧
        ((g : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty}
      = Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} // g ≠ e ∧ g ≠ f ∧
        (g : Set (Fin n)) ∩ (e : Set (Fin n)) ≠ (∅ : Set (Fin n)) ∧
        (g : Set (Fin n)) ∩ (f : Set (Fin n)) ≠ (∅ : Set (Fin n))} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun g => ?_))
  simp only [Set.nonempty_iff_ne_empty]

/-- From a real bound `(K : ℝ) ≤ n - 2` one gets the integer bound `K ≤ n - 2`. -/
private lemma nat_le_sub_two_of_real {n K : ℕ} (h : (K : ℝ) ≤ (n : ℝ) - 2) : K ≤ n - 2 := by
  have h2 : ((K + 2 : ℕ) : ℝ) ≤ (n : ℝ) := by push_cast; linarith
  have h3 : K + 2 ≤ n := by exact_mod_cast h2
  omega

/-- `Nat.card` of a subtype of a finite type is the cardinality of the associated
filtered finset. -/
private lemma natCard_subtype_eq_card_filter {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    Nat.card {x : α // p x} = (Finset.univ.filter p).card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-! ## The main lemma -/

theorem exists_pairing_of_size_k_family {n k t t₀ : ℕ} (𝓗 : Set (Set (Fin n))) {δ : ℝ}
    (Ap : Finset {e : Set (Fin n) // e ∈ 𝓗})
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 10 ^ 8) (hn : 1000000 ≤ n) (hk4 : 4 ≤ k)
    (hksq : (k : ℝ) ≤ Real.sqrt n + 1) (hklow : Real.sqrt n - 1 ≤ (k : ℝ))
    (hlin : ∀ e₁ ∈ 𝓗, ∀ e₂ ∈ 𝓗, e₁ ≠ e₂ → (e₁ ∩ e₂).Subsingleton)
    (hAp : ∀ e ∈ Ap, (e : Set (Fin n)).ncard = k)
    (hAminus : (Nat.card {e : {e : Set (Fin n) // e ∈ 𝓗} //
        (e : Set (Fin n)).ncard ≤ k - 1} : ℝ) ≤ 15 * (Ap.card : ℝ) / Real.sqrt n)
    (hbig : 20 * Real.sqrt n < (Ap.card : ℝ))
    (ht : 2 * (t : ℝ) * Real.sqrt n < 8 * (Ap.card : ℝ))
    (hcard : n + t ≤ Nat.card {e : Set (Fin n) // e ∈ 𝓗})
    (σ₀ : Fin t₀ → Fin 2 → {e : Set (Fin n) // e ∈ 𝓗})
    (hinj₀ : Function.Injective (fun p : Fin t₀ × Fin 2 => σ₀ p.1 p.2))
    (hdisj₀ : ∀ i : Fin t₀, Disjoint ((σ₀ i 0).1 : Set (Fin n)) ((σ₀ i 1).1 : Set (Fin n)))
    (hclique₀ : ∀ x : {e : Set (Fin n) // e ∈ 𝓗},
      x ∉ Set.range (fun p : Fin t₀ × Fin 2 => σ₀ p.1 p.2) →
      ∀ y : {e : Set (Fin n) // e ∈ 𝓗},
        y ∉ Set.range (fun p : Fin t₀ × Fin 2 => σ₀ p.1 p.2) → x ≠ y →
        ((x.1 : Set (Fin n)) ∩ y.1).Nonempty)
    (ht₀ : t₀ < t)
    (hcrit : ∀ e f : {e : Set (Fin n) // e ∈ 𝓗}, e ≠ f → (e : Set (Fin n)).ncard = k →
      (f : Set (Fin n)).ncard = k → ∀ w ∈ (e : Set (Fin n)) ∩ (f : Set (Fin n)),
        (Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} //
          (g : Set (Fin n)).ncard ≤ k - 1 ∧ w ∈ (g : Set (Fin n))} : ℝ) < 1 / (4 * δ) →
        (Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} // g ≠ e ∧ g ≠ f ∧
          (g : Set (Fin n)) ∩ (e : Set (Fin n)) ≠ (∅ : Set (Fin n)) ∧
            (g : Set (Fin n)) ∩ (f : Set (Fin n)) ≠ (∅ : Set (Fin n))} : ℝ) ≤ (n : ℝ) - 2) :
    ∃ σ : Fin t → Fin 2 → {e : Set (Fin n) // e ∈ 𝓗},
      Function.Injective (fun p : Fin t × Fin 2 => σ p.1 p.2) ∧
      (∀ i : Fin t, Disjoint ((σ i 0).1 : Set (Fin n)) ((σ i 1).1 : Set (Fin n))) := by
  classical
  haveI : Fintype {e : Set (Fin n) // e ∈ 𝓗} :=
    Fintype.subtype (Finset.univ.filter (fun e : Set (Fin n) => e ∈ 𝓗)) (by intro e; simp)
  have hn1 : 1 ≤ n := by omega
  let cnt : Fin n → ℕ := fun x =>
    Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} // (g : Set (Fin n)).ncard ≤ k - 1 ∧ x ∈ (g : Set (Fin n))}
  let Vbad : Finset (Fin n) := Finset.univ.filter (fun x => 1 / (4 * δ) ≤ (cnt x : ℝ))
  let Aminus : Finset {e : Set (Fin n) // e ∈ 𝓗} :=
    Finset.univ.filter (fun e : {e : Set (Fin n) // e ∈ 𝓗} => (e : Set (Fin n)).ncard ≤ k - 1)
  let cover : Finset {e : Set (Fin n) // e ∈ 𝓗} :=
    (Finset.univ : Finset (Fin t₀ × Fin 2)).image (fun p => σ₀ p.1 p.2)
  let Astar : Finset {e : Set (Fin n) // e ∈ 𝓗} :=
    Ap.filter (fun e : {e : Set (Fin n) // e ∈ 𝓗} => Real.sqrt (δ * n) ≤
      (((e : Set (Fin n)) ∩ (Vbad : Set (Fin n))).ncard : ℝ))
  let C : Finset {e : Set (Fin n) // e ∈ 𝓗} := Ap \ (Astar ∪ cover)
  -- ## Numeric facts
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsqrtn_ge : (1000 : ℝ) ≤ Real.sqrt n := by
    have h : (1000 : ℝ) ^ 2 ≤ (n : ℝ) := by
      have : ((1000000 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      norm_num at this ⊢
      exact this
    exact Real.le_sqrt_of_sq_le h
  have hspos : 0 < Real.sqrt n := by linarith
  have hdelta_sqrt_le : Real.sqrt δ ≤ 1 / 10000 := by
    have h1 : Real.sqrt δ ≤ Real.sqrt (1 / 10 ^ 8 : ℝ) := Real.sqrt_le_sqrt hδsmall
    have h2 : Real.sqrt (1 / 10 ^ 8 : ℝ) = 1 / 10000 := by
      rw [show (1 / 10 ^ 8 : ℝ) = (1 / 10000) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  have hksub1 : (k : ℝ) - 1 ≤ Real.sqrt n := by linarith [hksq]
  have hkn : Real.sqrt n / 2 ≤ (k : ℝ) - 1 := by linarith [hklow, hsqrtn_ge]
  have hk2 : 2 ≤ k := by omega
  have hk1R : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    linarith
  -- ## Bound on `|Vbad|`
  have hcnt : ∀ x, cnt x = (Aminus.filter (fun g : {g : Set (Fin n) // g ∈ 𝓗} => x ∈ (g : Set (Fin n)))).card := by
    intro x
    simp only [cnt, Aminus]
    rw [natCard_subtype_eq_card_filter
      (fun g : {g : Set (Fin n) // g ∈ 𝓗} => (g : Set (Fin n)).ncard ≤ k - 1 ∧ x ∈ (g : Set (Fin n)))]
    rw [Finset.filter_filter]
  have hAm : Aminus.card = Nat.card {e : {e : Set (Fin n) // e ∈ 𝓗} //
      (e : Set (Fin n)).ncard ≤ k - 1} := by
    simp only [Aminus]
    exact (natCard_subtype_eq_card_filter
      (fun e : {e : Set (Fin n) // e ∈ 𝓗} => (e : Set (Fin n)).ncard ≤ k - 1)).symm
  have hAminus_real : (Aminus.card : ℝ) ≤ 15 * (Ap.card : ℝ) / Real.sqrt n := by
    rw [hAm]; exact hAminus
  have hVbad_lower : (Vbad.card : ℝ) * (1 / (4 * δ)) ≤ ∑ x ∈ Vbad, (cnt x : ℝ) := by
    have h1 : ∑ x ∈ Vbad, (1 / (4 * δ) : ℝ) ≤ ∑ x ∈ Vbad, (cnt x : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      simp only [Vbad, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hx
    have h2 : ∑ x ∈ Vbad, (1 / (4 * δ) : ℝ) = (Vbad.card : ℝ) * (1 / (4 * δ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    linarith
  have hstep1N : ∑ x ∈ Vbad, cnt x
      = ∑ g ∈ Aminus, (Vbad.filter (fun x => x ∈ (g : Set (Fin n)))).card := by
    have h1 : ∑ x ∈ Vbad, cnt x
        = ∑ x ∈ Vbad, (Aminus.filter (fun g : {g : Set (Fin n) // g ∈ 𝓗} => x ∈ (g : Set (Fin n)))).card :=
      Finset.sum_congr rfl (fun x _ => hcnt x)
    rw [h1]
    exact Commons.Data.Finset.sum_card_filter_comm Vbad Aminus (fun x g => x ∈ (g : Set (Fin n)))
  have hVbad_upperA : ∑ x ∈ Vbad, (cnt x : ℝ)
      = ∑ g ∈ Aminus, ((Vbad.filter (fun x => x ∈ (g : Set (Fin n)))).card : ℝ) := by
    have := congrArg (Nat.cast : ℕ → ℝ) hstep1N
    push_cast at this
    exact this
  have hstep2 : ∀ g ∈ Aminus, ((Vbad.filter (fun x => x ∈ (g : Set (Fin n)))).card : ℝ) ≤ (k : ℝ) - 1 := by
    intro g hg
    have hgsize : (g : Set (Fin n)).ncard ≤ k - 1 := by
      simp only [Aminus, Finset.mem_filter, Finset.mem_univ, true_and] at hg
      exact hg
    have hle : (Vbad.filter (fun x => x ∈ (g : Set (Fin n)))).card ≤ (g : Set (Fin n)).ncard := by
      rw [← Set.ncard_coe_finset (Vbad.filter (fun x => x ∈ (g : Set (Fin n))))]
      refine Set.ncard_le_ncard ?_ (Set.toFinite _)
      intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter] at hx
      exact hx.2
    have : (Vbad.filter (fun x => x ∈ (g : Set (Fin n)))).card ≤ k - 1 := le_trans hle hgsize
    have hkc : (k : ℝ) - 1 = ((k - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ k)]; norm_num
    rw [hkc]
    exact_mod_cast this
  have hVbad_upper : ∑ x ∈ Vbad, (cnt x : ℝ) ≤ (Aminus.card : ℝ) * ((k : ℝ) - 1) := by
    rw [hVbad_upperA]
    calc ∑ g ∈ Aminus, ((Vbad.filter (fun x => x ∈ (g : Set (Fin n)))).card : ℝ)
        ≤ ∑ g ∈ Aminus, ((k : ℝ) - 1) := Finset.sum_le_sum hstep2
      _ = (Aminus.card : ℝ) * ((k : ℝ) - 1) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hVbad_bound : (Vbad.card : ℝ) * (1 / (4 * δ)) ≤ (Aminus.card : ℝ) * ((k : ℝ) - 1) :=
    le_trans hVbad_lower hVbad_upper
  have hVbad_le : (Vbad.card : ℝ) ≤ 60 * δ * (Ap.card : ℝ) := by
    have h1 : (Aminus.card : ℝ) * ((k : ℝ) - 1) ≤ 15 * (Ap.card : ℝ) := by
      calc (Aminus.card : ℝ) * ((k : ℝ) - 1)
          ≤ (15 * (Ap.card : ℝ) / Real.sqrt n) * Real.sqrt n :=
            mul_le_mul hAminus_real hksub1 (le_of_lt hk1R) (by positivity)
        _ = 15 * (Ap.card : ℝ) := by rw [div_mul_cancel₀ _ (ne_of_gt hspos)]
    have h2 : (Vbad.card : ℝ) * (1 / (4 * δ)) ≤ 15 * (Ap.card : ℝ) := le_trans hVbad_bound h1
    have h4dpos : 0 < 4 * δ := by linarith
    have hvdiv : (Vbad.card : ℝ) / (4 * δ) ≤ 15 * (Ap.card : ℝ) := by
      rw [div_eq_mul_one_div]; exact h2
    have hv : (Vbad.card : ℝ) ≤ 15 * (Ap.card : ℝ) * (4 * δ) := (div_le_iff₀ h4dpos).mp hvdiv
    nlinarith [hv]
  -- ## Bound on `|A*|`
  let Aimg : Finset (Set (Fin n)) := Ap.image Subtype.val
  have hAimg_size : ∀ e ∈ Aimg, e.ncard = k := by
    intro e he
    simp only [Aimg, Finset.mem_image] at he
    obtain ⟨g, hg, rfl⟩ := he
    exact hAp g hg
  have hAimg_lin : ∀ e ∈ Aimg, ∀ f ∈ Aimg, e ≠ f → (e ∩ f).Subsingleton := by
    intro e he f hf hef
    simp only [Aimg, Finset.mem_image] at he hf
    obtain ⟨g, hg, hge⟩ := he
    obtain ⟨h, hh, hhf⟩ := hf
    rw [← hge, ← hhf]
    apply hlin g.1 g.2 h.1 h.2
    intro hgh
    exact hef (by rw [← hge, ← hhf, hgh])
  have hdeg_eq : ∀ x, Set.ncard {e : Set (Fin n) | e ∈ (Aimg : Set (Set (Fin n))) ∧ x ∈ e}
      = (Ap.filter (fun g : {g : Set (Fin n) // g ∈ 𝓗} => x ∈ (g : Set (Fin n)))).card := by
    intro x
    have hset : {e : Set (Fin n) | e ∈ (Aimg : Set (Set (Fin n))) ∧ x ∈ e}
        = Subtype.val '' (↑(Ap.filter (fun g : {g : Set (Fin n) // g ∈ 𝓗} => x ∈ (g : Set (Fin n)))) : Set {e : Set (Fin n) // e ∈ 𝓗}) := by
      ext e; constructor
      · intro he
        obtain ⟨heA, hxe⟩ := he
        rw [Finset.mem_coe] at heA
        simp only [Aimg, Finset.mem_image] at heA
        obtain ⟨g, hg, hge⟩ := heA
        exact ⟨g, by simp only [Finset.mem_coe, Finset.mem_filter]; exact ⟨hg, by rw [hge]; exact hxe⟩, hge⟩
      · rintro ⟨g, hg, rfl⟩
        simp only [Finset.mem_coe, Finset.mem_filter] at hg
        exact ⟨by rw [Finset.mem_coe]; exact Finset.mem_image.mpr ⟨g, hg.1, rfl⟩, hg.2⟩
    rw [hset, Set.ncard_image_of_injective _ Subtype.coe_injective, Set.ncard_coe_finset]
  have hdeg_bound : ∀ x, ((Ap.filter (fun g : {g : Set (Fin n) // g ∈ 𝓗} => x ∈ (g : Set (Fin n)))).card : ℝ) ≤ 2 * Real.sqrt n := by
    intro x
    have h := ncard_le_two_sqrt Aimg hAimg_size hAimg_lin hk2 hn1 hkn x
    rwa [hdeg_eq x] at h
  have hAstar_lower : (Astar.card : ℝ) * Real.sqrt (δ * n)
      ≤ ∑ e ∈ Astar, (((e : Set (Fin n)) ∩ (Vbad : Set (Fin n))).ncard : ℝ) := by
    have h1 : ∑ e ∈ Astar, (Real.sqrt (δ * n))
        ≤ ∑ e ∈ Astar, (((e : Set (Fin n)) ∩ (Vbad : Set (Fin n))).ncard : ℝ) := by
      apply Finset.sum_le_sum
      intro e he
      simp only [Astar, Finset.mem_filter] at he
      exact he.2
    rwa [Finset.sum_const, nsmul_eq_mul] at h1
  have hAstar_upperN : ∑ e ∈ Astar, ((e : Set (Fin n)) ∩ (Vbad : Set (Fin n))).ncard
      ≤ ∑ x ∈ Vbad, (Ap.filter (fun g : {g : Set (Fin n) // g ∈ 𝓗} => x ∈ (g : Set (Fin n)))).card := by
    have hset : ∀ e : {e : Set (Fin n) // e ∈ 𝓗}, ((e : Set (Fin n)) ∩ (Vbad : Set (Fin n))).ncard
        = (Vbad.filter (fun x => x ∈ (e : Set (Fin n)))).card := by
      intro e
      rw [← Set.ncard_coe_finset (Vbad.filter (fun x => x ∈ (e : Set (Fin n))))]
      congr 1
      ext x
      simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_inter_iff]
      tauto
    simp only [hset]
    rw [Commons.Data.Finset.sum_card_filter_comm Astar Vbad (fun e x => x ∈ (e : Set (Fin n)))]
    apply Finset.sum_le_sum
    intro x hx
    have hAstar_sub : Astar ⊆ Ap := by
      intro e he; simp only [Astar] at he; exact Finset.mem_of_mem_filter e he
    exact Finset.card_le_card (Finset.filter_subset_filter _ hAstar_sub)
  have hAstar_upper : ∑ e ∈ Astar, (((e : Set (Fin n)) ∩ (Vbad : Set (Fin n))).ncard : ℝ)
      ≤ ∑ x ∈ Vbad, (((Ap.filter (fun g : {g : Set (Fin n) // g ∈ 𝓗} => x ∈ (g : Set (Fin n)))).card : ℕ) : ℝ) := by
    have := hAstar_upperN
    exact_mod_cast this
  have hAstar_sum_le : ∑ e ∈ Astar, (((e : Set (Fin n)) ∩ (Vbad : Set (Fin n))).ncard : ℝ)
      ≤ (Vbad.card : ℝ) * (2 * Real.sqrt n) := by
    calc ∑ e ∈ Astar, (((e : Set (Fin n)) ∩ (Vbad : Set (Fin n))).ncard : ℝ)
        ≤ ∑ x ∈ Vbad, (((Ap.filter (fun g : {g : Set (Fin n) // g ∈ 𝓗} => x ∈ (g : Set (Fin n)))).card : ℕ) : ℝ) := hAstar_upper
      _ ≤ ∑ x ∈ Vbad, (2 * Real.sqrt n) := Finset.sum_le_sum (fun x _ => hdeg_bound x)
      _ = (Vbad.card : ℝ) * (2 * Real.sqrt n) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hAstar_bound : (Astar.card : ℝ) * Real.sqrt (δ * n)
      ≤ (Vbad.card : ℝ) * (2 * Real.sqrt n) := le_trans hAstar_lower hAstar_sum_le
  have hAstar_le : (Astar.card : ℝ) ≤ (1 / 20) * (Ap.card : ℝ) := by
    have hsdn : Real.sqrt (δ * n) = Real.sqrt δ * Real.sqrt n := Real.sqrt_mul (le_of_lt hδ) n
    have hsdpos : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
    have h1 : (Astar.card : ℝ) * (Real.sqrt δ * Real.sqrt n) ≤ (Vbad.card : ℝ) * (2 * Real.sqrt n) := by
      rwa [← hsdn]
    have h2 : (Astar.card : ℝ) * Real.sqrt δ ≤ 2 * (Vbad.card : ℝ) := by
      rw [← mul_assoc] at h1
      rw [show (Vbad.card : ℝ) * (2 * Real.sqrt n) = (2 * (Vbad.card : ℝ)) * Real.sqrt n by ring] at h1
      exact (mul_le_mul_iff_of_pos_right hspos).mp h1
    have h3 : (Astar.card : ℝ) * Real.sqrt δ ≤ 120 * δ * (Ap.card : ℝ) := by
      nlinarith [h2, hVbad_le]
    have hsdsq : Real.sqrt δ * Real.sqrt δ = δ := by rw [← sq, Real.sq_sqrt (le_of_lt hδ)]
    have h5 : (Astar.card : ℝ) ≤ 120 * Real.sqrt δ * (Ap.card : ℝ) := by
      have heq : 120 * δ * (Ap.card : ℝ) / Real.sqrt δ = 120 * Real.sqrt δ * (Ap.card : ℝ) := by
        rw [div_eq_iff (ne_of_gt hsdpos)]
        nlinarith [hsdsq]
      rw [← heq]
      exact (le_div_iff₀ hsdpos).mpr (by linarith [h3])
    nlinarith [h5, hdelta_sqrt_le, (Nat.cast_nonneg Ap.card : (0 : ℝ) ≤ (Ap.card : ℝ))]
  -- ## The clique `C` is large
  have hcover_card : cover.card = 2 * t₀ := by
    simp only [cover]
    rw [Finset.card_image_of_injective _ hinj₀, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin]
    ring
  have hAp_sub : Ap.card ≤ C.card + (Astar ∪ cover).card := by
    have hsub : Ap ⊆ C ∪ (Astar ∪ cover) := by
      intro e he
      by_cases h : e ∈ Astar ∪ cover
      · exact Finset.mem_union_right _ h
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he, h⟩)
    calc Ap.card ≤ (C ∪ (Astar ∪ cover)).card := Finset.card_le_card hsub
      _ ≤ C.card + (Astar ∪ cover).card := Finset.card_union_le _ _
  have hC_lower : (19 / 20) * (Ap.card : ℝ) - 2 * (t : ℝ) + 2 ≤ (C.card : ℝ) := by
    have h1 : (Ap.card : ℝ) ≤ (C.card : ℝ) + ((Astar ∪ cover).card : ℝ) := by exact_mod_cast hAp_sub
    have h2 : ((Astar ∪ cover).card : ℝ) ≤ (Astar.card : ℝ) + (cover.card : ℝ) := by
      have := Finset.card_union_le Astar cover; exact_mod_cast this
    have h4 : (cover.card : ℝ) = 2 * (t₀ : ℝ) := by rw [hcover_card]; push_cast; ring
    have h5 : (t₀ : ℝ) ≤ (t : ℝ) - 1 := by
      have ht1 : 1 ≤ t := by omega
      have : (t₀ : ℝ) ≤ ((t - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : t₀ ≤ t - 1)
      rwa [Nat.cast_sub ht1, Nat.cast_one] at this
    linarith [h1, h2, hAstar_le, h4, h5]
  have h4t' : 4 * (t : ℝ) < 16 * (Ap.card : ℝ) / Real.sqrt n := by
    rw [lt_div_iff₀ hspos]
    nlinarith [ht]
  have hnum : 16 * (Ap.card : ℝ) / Real.sqrt n < (19 / 20) * (Ap.card : ℝ) + 2 - 4 * Real.sqrt n := by
    have hdiv : 16 * (Ap.card : ℝ) / Real.sqrt n ≤ (16 / 1000) * (Ap.card : ℝ) := by
      have hh := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 16 * (Ap.card : ℝ) by positivity)
        (by norm_num : (0 : ℝ) < 1000) hsqrtn_ge
      rw [show (16 * (Ap.card : ℝ)) / 1000 = (16 / 1000) * (Ap.card : ℝ) by ring] at hh
      exact hh
    nlinarith [hdiv, hbig, hsqrtn_ge]
  have hC_card : 4 * Real.sqrt n + 2 * (t : ℝ) ≤ (C.card : ℝ) := by
    linarith [h4t', hnum, hC_lower]
  -- ## Applying the two imported lemmas
  have hsizeC : ∀ e ∈ C, (e : Set (Fin n)).ncard = k := by
    intro e he
    exact hAp e (Finset.mem_sdiff.mp he).1
  have hbadC : ∀ e ∈ C, (k : ℝ) - Real.sqrt (δ * n)
      ≤ (((e : Set (Fin n)) \ (Vbad : Set (Fin n))).ncard : ℝ) := by
    intro e he
    have heAp : e ∈ Ap := (Finset.mem_sdiff.mp he).1
    have hneAstar : e ∉ Astar := fun hm =>
      (Finset.mem_sdiff.mp he).2 (Finset.mem_union_left _ hm)
    have hnot : ¬ (Real.sqrt (δ * n) ≤ (((e : Set (Fin n)) ∩ (Vbad : Set (Fin n))).ncard : ℝ)) := by
      intro hle
      exact hneAstar (by simp only [Astar, Finset.mem_filter]; exact ⟨heAp, hle⟩)
    have hlt : (((e : Set (Fin n)) ∩ (Vbad : Set (Fin n))).ncard : ℝ) < Real.sqrt (δ * n) :=
      not_le.mp hnot
    have hsize : (e : Set (Fin n)).ncard = k := hAp e heAp
    have hkey : ((e : Set (Fin n)) ∩ (Vbad : Set (Fin n))).ncard
        + ((e : Set (Fin n)) \ (Vbad : Set (Fin n))).ncard = (e : Set (Fin n)).ncard :=
      Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _
    have hmk : ((e : Set (Fin n)) ∩ (Vbad : Set (Fin n))).ncard ≤ k := by
      rw [← hsize]; exact Set.ncard_le_ncard Set.inter_subset_left
    have hfin : ((e : Set (Fin n)) \ (Vbad : Set (Fin n))).ncard
        = k - ((e : Set (Fin n)) ∩ (Vbad : Set (Fin n))).ncard := by omega
    rw [hfin, Nat.cast_sub hmk]
    linarith [hlt]
  have hcritC : ∀ e ∈ C, ∀ f ∈ C, e ≠ f →
      (∃ w ∈ (e : Set (Fin n)) ∩ (f : Set (Fin n)), w ∉ (Vbad : Set (Fin n))) →
      (Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} // g ≠ e ∧ g ≠ f ∧
          (g : Set (Fin n)) ∩ (e : Set (Fin n)) ≠ (∅ : Set (Fin n)) ∧
            (g : Set (Fin n)) ∩ (f : Set (Fin n)) ≠ (∅ : Set (Fin n))} : ℝ) ≤ (n : ℝ) - 2 := by
    intro e he f hf hef ⟨w, hw, hwbad⟩
    have heAp : e ∈ Ap := (Finset.mem_sdiff.mp he).1
    have hfAp : f ∈ Ap := (Finset.mem_sdiff.mp hf).1
    have hlt : (Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} // (g : Set (Fin n)).ncard ≤ k - 1 ∧
        w ∈ (g : Set (Fin n))} : ℝ) < 1 / (4 * δ) := by
      have hmem : w ∉ Vbad := fun hw' => hwbad (Finset.mem_coe.mpr hw')
      have : ¬ (1 / (4 * δ) ≤ (cnt w : ℝ)) := by
        intro hle
        exact hmem (by simp only [Vbad, Finset.mem_filter, Finset.mem_univ, true_and]; exact hle)
      exact not_le.mp this
    exact hcrit e f hef (hAp e heAp) (hAp f hfAp) w hw hlt
  have hkB : Real.sqrt n / 2 ≤ (k : ℝ) - Real.sqrt (δ * n) := by
    have hsdn : Real.sqrt (δ * n) = Real.sqrt δ * Real.sqrt n := Real.sqrt_mul (le_of_lt hδ) n
    have hb : Real.sqrt δ * Real.sqrt n ≤ (1 / 10000) * Real.sqrt n :=
      mul_le_mul_of_nonneg_right hdelta_sqrt_le (Real.sqrt_nonneg n)
    rw [hsdn]
    nlinarith [hklow, hb, hsqrtn_ge]
  obtain ⟨a, ha_inj, ha_memC, _ha_meetC, ha_usefulR⟩ :=
    exists_useful_pairs_in_clique (δ := δ) (B := Real.sqrt (δ * n)) 𝓗 k t Vbad
      le_rfl hkB hδ hn1 C hC_card hsizeC hbadC hcritC
  have huseful : ∀ i : Fin t, Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} // g ≠ a i 0 ∧ g ≠ a i 1 ∧
      ((g : Set (Fin n)) ∩ (a i 0).1).Nonempty ∧ ((g : Set (Fin n)) ∩ (a i 1).1).Nonempty} ≤ n - 2 := by
    intro i
    have h := ha_usefulR i
    rw [← useful_card_eq 𝓗 (a i 0) (a i 1)] at h
    exact nat_le_sub_two_of_real h
  have hcover_range : ∀ x, x ∈ cover ↔ x ∈ Set.range (fun p : Fin t₀ × Fin 2 => σ₀ p.1 p.2) := by
    intro x
    simp only [cover, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]
  have hinter : ∀ p q : Fin t × Fin 2, p ≠ q →
      (((a p.1 p.2).1 : Set (Fin n)) ∩ ((a q.1 q.2).1 : Set (Fin n))).Nonempty := by
    intro p q hpq
    have hmem : ∀ r : Fin t × Fin 2, a r.1 r.2 ∈ C := by
      intro r
      rcases r with ⟨i, b⟩
      fin_cases b
      · exact (ha_memC i).1
      · exact (ha_memC i).2
    have hp : a p.1 p.2 ∉ Set.range (fun r : Fin t₀ × Fin 2 => σ₀ r.1 r.2) := by
      intro hr
      have hnotc : a p.1 p.2 ∉ cover := fun hc =>
        (Finset.mem_sdiff.mp (hmem p)).2 (Finset.mem_union_right _ hc)
      exact hnotc ((hcover_range _).mpr hr)
    have hq : a q.1 q.2 ∉ Set.range (fun r : Fin t₀ × Fin 2 => σ₀ r.1 r.2) := by
      intro hr
      have hnotc : a q.1 q.2 ∉ cover := fun hc =>
        (Finset.mem_sdiff.mp (hmem q)).2 (Finset.mem_union_right _ hc)
      exact hnotc ((hcover_range _).mpr hr)
    have hne : a p.1 p.2 ≠ a q.1 q.2 := fun h => hpq (ha_inj h)
    exact hclique₀ _ hp _ hq hne
  exact pairing_of_useful_pairs 𝓗 t a ha_inj hinter huseful hcard


end Commons.Combinatorics.Hypergraph
