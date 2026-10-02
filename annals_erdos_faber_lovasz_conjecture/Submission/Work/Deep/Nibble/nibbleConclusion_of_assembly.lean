import Submission.Work.Deep.Nibble.AsmBase
import Submission.Work.Deep.Nibble.asmStep

set_option autoImplicit false
open scoped BigOperators

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

local notation "Hypergraph" => ErdosFaberLovaszConjecture.Hypergraph

noncomputable section

theorem nibbleConclusion_of_assembly
    {n : ℕ} {𝓗 𝓗' : MultiHypergraph n} {R : Hypergraph (Fin n)}
    {𝓥 : Set (Set (Fin n))} {U S : Set (Fin n)}
    {ρ γ β ξ ε : ℝ} {D r : ℕ} (M : Fin D → Set (Set (Fin n)))
    (hU : U = VplusTwo (MultiHypergraph.pow2 𝓗) (1 - ε))
    (hSsub : S ⊆ U)
    (hC1 : (1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ) → (D : ℝ) + γ * (n : ℝ) ≤ (S.ncard : ℝ))
    (hU𝓥 : U ∈ 𝓥) (huniv𝓥 : (Set.univ : Set (Fin n)) ∈ 𝓥)
    (habs : IsAbsorber (incidentTwo (MultiHypergraph.pow2 𝓗) U) R 𝓥 ρ γ ξ)
    (hlinH : 𝓗.IsLinear)
    (hle : 𝓗' ≤ 𝓗) (hout : ∀ e ∈ 𝓗'.edges, e ∉ R) (hlin' : 𝓗'.IsLinear)
    (hsize : ∀ e ∈ 𝓗'.edges, edgeSize e ≤ r)
    (hdeg : ∀ w : Fin n, |((𝓗'.deg w : ℝ)) - (D : ℝ)| ≤ β * (D : ℝ))
    (hMmatch : ∀ i, MultiHypergraph.IsMatching 𝓗 (M i))
    (hMdisj : ∀ i j, i ≠ j → EdgeDisjointFam (M i) (M j))
    (hMout : ∀ i, ∀ e ∈ M i, e ∉ 𝓗'.edgeSet)
    (hMR : ∀ i, ∀ e ∈ M i, e ∉ R)
    (hMsz : ∀ i, ((famVert (M i)).ncard : ℝ) ≤ β * (D : ℝ))
    (hMint : ∀ e ∈ 𝓗'.edgeSet,
      (({i : Fin D | (e ∩ famVert (M i)).Nonempty}).ncard : ℝ) ≤ β * (D : ℝ))
    {κ γp δ βp : ℝ} {K : ℕ}
    (hpar : AssemblyParams n (D : ℝ) β γ ε ρ ξ κ γp δ βp K)
    (hint : InternalMargins n ρ ε γp κ ξ)
    (hcross : CrossingMargins n ρ ε γp κ ξ)
    (P : EdgePartition 𝓗' K)
    (I : Fin K → Finset (Fin D))
    (hIcard : ∀ i, D / K ≤ (I i).card ∧ (I i).card ≤ D / K + 1)
    (hIdisj : ∀ i j, i ≠ j → Disjoint (I i) (I j))
    (hIuniv : Finset.univ.biUnion I = Finset.univ)
    (hKslide : (n : ℝ) ^ ((1 : ℝ) / 2) + 1 ≤ (D : ℝ) / (K : ℝ))
    (hpartdeg : ∀ i w, |(((P.part i).deg w : ℝ)) - ((I i).card : ℝ)|
      ≤ βp * ((I i).card : ℝ))
    (hseed : ∀ i c, c ∈ I i → ((famVert (M c)).ncard : ℝ) ≤ βp * ((I i).card : ℝ))
    (hint' : ∀ i e, e ∈ (P.part i).edgeSet →
      (({c : Fin D | c ∈ I i ∧ (e ∩ famVert (M c)).Nonempty}).ncard : ℝ)
        ≤ βp * ((I i).card : ℝ))
    (hPMS : PseudorandomMatchingAtObj n r βp κ γp) :
    NibbleConclusion (U := U) (S := S) (γ := γ) (β := β) (ε := ε) 𝓗 𝓗' R M := by  classical
  -- the slack constant for the pseudorandomness error
  set κa : ℝ := slackκ κ βp n with hκa
  have hκ0 : 0 < κ := hpar.hκ0
  have hβp0 : 0 ≤ βp := le_of_lt hpar.hβp0
  have hβp1 : βp ≤ 1 := hpar.hβp1
  have hγp0 : 0 < γp := hpar.hγp0
  have hγp1 : γp ≤ 1 := by nlinarith [hint.hγρ, hint.hρ1]
  have hκ1 : κ ≤ 1 := by nlinarith [hint.hκγ, hγp1]
  have hβp10 : βp ≤ 1 / 10 := by nlinarith [hpar.hβpκ, hκ1]
  have hγ4 : γ ≤ 4 := by nlinarith [hpar.hγpγ, hγp1]
  have hκ16 : κ ≤ 1 / 6 := by nlinarith [hint.hκγ, hint.hγρ, hint.hρ1]
  have hε12 : ε ≤ 1 / 2 := by nlinarith [hint.hε4]
  have hρ0 : 0 < ρ := hint.hρ
  have hDn : D < n := by
    have h := hpar.hKround
    have h1 : (0 : ℝ) < (n : ℝ) - D := by
      by_contra hcon
      have : κ * ((n : ℝ) - D) ≤ 0 := by nlinarith [hκ0, not_lt.mp hcon]
      linarith
    have h2 : (D : ℝ) < (n : ℝ) := by linarith
    exact_mod_cast h2
  have hnpos : (1 : ℝ) ≤ (n : ℝ) := by
    have : 1 ≤ n := by omega
    exact_mod_cast this
  have hκn2 : 2 ≤ κ * (n : ℝ) := by
    have h1 : (n : ℝ) ^ ((1 : ℝ) / 2) + 1 ≤ κ * (D : ℝ) := hpar.hKfloor
    have h2 : (D : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_of_lt hDn
    have h3 : (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow hnpos (by norm_num)
    have h4 : κ * (D : ℝ) ≤ κ * (n : ℝ) := mul_le_mul_of_nonneg_left h2 (le_of_lt hκ0)
    linarith
  have hκn1 : 1 ≤ κ * (n : ℝ) := by linarith
  have hintA : InternalMargins n ρ ε γp κa ξ := by
    rw [hκa]; exact internalMargins_slack hκn2 hβp0 hβp10 hint hpar.hκγ2'
  have hcrossA : CrossingMargins n ρ ε γp κa ξ := by
    rw [hκa]; exact crossingMargins_slack hκn2 hβp0 hβp10 hint hcross
  have hγpγ6 : γ + 6 * γp ≤ 10 * γp := by linarith [hpar.hγpγ]
  have hprocCard : ∀ k : Fin K, ((I k).card : ℝ) ≤ κ * (n : ℝ) + 1 := by
    intro k
    have h1 := (hIcard k).2
    have h2 : ((D / K : ℕ) : ℝ) ≤ κ * (n : ℝ) := by
      have h3 : (D : ℝ) ≤ κ * (n : ℝ) * (K : ℝ) := hpar.hKup
      have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num) hpar.hK)
      have h4 : (D : ℝ) / (K : ℝ) ≤ κ * (n : ℝ) := by
        rw [div_le_iff₀ hK0]; linarith
      have h5 : ((D / K : ℕ) : ℝ) ≤ (D : ℝ) / (K : ℝ) := Nat.cast_div_le
      linarith
    have : ((I k).card : ℝ) ≤ ((D / K : ℕ) : ℝ) + 1 := by exact_mod_cast h1
    linarith
  have hblock_le_n : ∀ k : Fin K, ((I k).card : ℝ) ≤ (n : ℝ) := by
    intro k
    have h1 : ((I k).card : ℝ) ≤ κ * (n : ℝ) + 1 := hprocCard k
    have h2 : κ * (n : ℝ) + 1 ≤ (n : ℝ) := by nlinarith [hκn2, hnpos, hκ16]
    linarith
  have hblock_ge_sqrt : ∀ k : Fin K, (n : ℝ) ^ ((1 : ℝ) / 2) ≤ ((I k).card : ℝ) := by
    intro k
    have hKpos : 0 < K := Nat.lt_of_lt_of_le (by norm_num) hpar.hK
    have hlt : D < (D / K + 1) * K :=
      (Nat.div_lt_iff_lt_mul hKpos).mp (Nat.lt_succ_self _)
    have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
    have hcast : (D : ℝ) / (K : ℝ) < ((D / K : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hK0]
      have h2 : ((D : ℕ) : ℝ) < (((D / K + 1) * K : ℕ) : ℝ) := by exact_mod_cast hlt
      push_cast at h2
      linarith
    have h3 : ((D / K : ℕ) : ℝ) ≤ ((I k).card : ℝ) := by exact_mod_cast (hIcard k).1
    have h1 : (n : ℝ) ^ ((1 : ℝ) / 2) + 1 ≤ (D : ℝ) / (K : ℝ) := hKslide
    linarith
  have hproc_le : ∀ j : ℕ, (Proc I j).card ≤ D := by
    intro j
    have h : Proc I j ⊆ Finset.univ := Finset.subset_univ _
    have := Finset.card_le_card h
    simpa using this
  -- numerical facts for the family bounds
  have hn8 : (8 : ℝ) ≤ (n : ℝ) := by
    have h1 : (2000 : ℝ) ≤ γp * ρ * (n : ℝ) := hint.hnbig
    have h2 : γp * ρ ≤ 1 / 20000 := by
      have h3 : γp ≤ 1 / 20000 := by nlinarith [hint.hγρ, hint.hρ1]
      nlinarith [h3, hint.hρ1, hint.hρ]
    by_contra hcon
    have h5 : (n : ℝ) < 8 := not_le.mp hcon
    have hγρ_nn : (0 : ℝ) < γp * ρ := by nlinarith [hγp0, hint.hρ]
    have h6 : γp * ρ * (n : ℝ) < γp * ρ * 8 := mul_lt_mul_of_pos_left h5 hγρ_nn
    have h7 : γp * ρ * 8 ≤ (1 / 20000) * 8 := by
      have := mul_le_mul_of_nonneg_right h2 (by norm_num : (0:ℝ) ≤ 8)
      linarith
    linarith
  have hn6 : (6 : ℝ) ≤ (n : ℝ) := by linarith [hn8]
  have hlog2 : (2 : ℝ) ≤ Real.log (n : ℝ) := by
    have h1 : Real.log 8 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hn8
    have h2 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    have h3 : (0.69 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
    linarith
  have hpow : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ Real.log (n : ℝ) := by
    have h1 : (1 : ℝ) < (n : ℝ) := by linarith
    exact (Real.rpow_le_rpow_left_iff h1).mpr hlog2
  have hfamV : (2 * (n : ℝ) + 3) * (κ * (n : ℝ) + 1) ≤ (n : ℝ) ^ Real.log (n : ℝ) := by
    have h1a : 2 * (n : ℝ) + 3 ≤ 3 * (n : ℝ) := by linarith
    have h1b : κ * (n : ℝ) + 1 ≤ (n : ℝ) / 3 := by nlinarith [hκ16, hn6]
    have h1 : (2 * (n : ℝ) + 3) * (κ * (n : ℝ) + 1) ≤ (3 * (n : ℝ)) * ((n : ℝ) / 3) :=
      mul_le_mul h1a h1b (by linarith) (by linarith)
    have h2 : (3 * (n : ℝ)) * ((n : ℝ) / 3) = (n : ℝ) ^ 2 := by ring
    calc (2 * (n : ℝ) + 3) * (κ * (n : ℝ) + 1) ≤ (3 * (n : ℝ)) * ((n : ℝ) / 3) := h1
      _ = (n : ℝ) ^ 2 := h2
      _ ≤ (n : ℝ) ^ (2 : ℝ) := le_of_eq (Real.rpow_two (n : ℝ)).symm
      _ ≤ (n : ℝ) ^ Real.log (n : ℝ) := hpow
  have hfamE : ((n : ℝ) + 1) ≤ (n : ℝ) ^ Real.log (n : ℝ) := by
    have h1 : (n : ℝ) + 1 ≤ (n : ℝ) ^ 2 := by nlinarith [hn8]
    calc (n : ℝ) + 1 ≤ (n : ℝ) ^ 2 := h1
      _ ≤ (n : ℝ) ^ (2 : ℝ) := le_of_eq (Real.rpow_two (n : ℝ)).symm
      _ ≤ (n : ℝ) ^ Real.log (n : ℝ) := hpow
  -- cardinality of the families handed to `lem:pseudorandom_matching`
  have habsorberCard : ∀ (R' : Hypergraph (Fin n)) (U' : Set (Fin n)),
      (absorberFam R' U').ncard ≤ 2 * n := by
    intro R' U'
    have h1 : absorberFam R' U' ⊆
        ((fun u : Fin n => nbrs R' u ∩ U') '' (Set.univ : Set (Fin n))) ∪
        ((fun u : Fin n => nbrs R' u \ U') '' (Set.univ : Set (Fin n))) := by
      rintro X (⟨u, rfl⟩ | ⟨u, rfl⟩)
      · exact Or.inl ⟨u, Set.mem_univ u, rfl⟩
      · exact Or.inr ⟨u, Set.mem_univ u, rfl⟩
    have h2 : (((fun u : Fin n => nbrs R' u ∩ U') '' (Set.univ : Set (Fin n))) ∪
        ((fun u : Fin n => nbrs R' u \ U') '' (Set.univ : Set (Fin n)))).ncard ≤ 2 * n := by
      have h3 := Set.ncard_union_le ((fun u : Fin n => nbrs R' u ∩ U') '' (Set.univ : Set (Fin n)))
        ((fun u : Fin n => nbrs R' u \ U') '' (Set.univ : Set (Fin n)))
      have h4 : ((fun u : Fin n => nbrs R' u ∩ U') '' (Set.univ : Set (Fin n))).ncard ≤ n := by
        have h := Set.ncard_image_le (s := (Set.univ : Set (Fin n)))
          (f := fun u : Fin n => nbrs R' u ∩ U') (Set.toFinite _)
        rwa [Set.ncard_univ, Nat.card_fin] at h
      have h5 : ((fun u : Fin n => nbrs R' u \ U') '' (Set.univ : Set (Fin n))).ncard ≤ n := by
        have h := Set.ncard_image_le (s := (Set.univ : Set (Fin n)))
          (f := fun u : Fin n => nbrs R' u \ U') (Set.toFinite _)
        rwa [Set.ncard_univ, Nat.card_fin] at h
      omega
    exact le_trans (Set.ncard_le_ncard h1 (Set.toFinite _)) h2
  have hshiftCard : ∀ (k : Fin K) (base : Set (Set (Fin n))) (B : ℕ),
      base.ncard ≤ B → (shiftFam I M k base).ncard ≤ B * (I k).card := by
    intro k base B hB
    have h1 : shiftFam I M k base ⊆
        (fun p : Set (Fin n) × Fin D => p.1 \ famVert (M p.2)) ''
          (base ×ˢ ((I k : Finset (Fin D)) : Set (Fin D))) := by
      rintro A ⟨X, hX, c, hc, rfl⟩
      exact ⟨(X, c), ⟨hX, Finset.mem_coe.mpr hc⟩, rfl⟩
    have h2 : (base ×ˢ ((I k : Finset (Fin D)) : Set (Fin D))).ncard
        = base.ncard * (I k).card := by
      rw [Set.ncard_prod]
      congr 1
      exact_mod_cast rfl
    calc (shiftFam I M k base).ncard
        ≤ (base ×ˢ ((I k : Finset (Fin D)) : Set (Fin D))).ncard :=
          le_trans (Set.ncard_le_ncard h1 (Set.toFinite _)) (Set.ncard_image_le (Set.toFinite _))
      _ = base.ncard * (I k).card := h2
      _ ≤ B * (I k).card := Nat.mul_le_mul_right _ hB
  -- the facts needed to start the induction
  have hProc0 : Proc I 0 = ∅ := by
    ext c; rw [mem_Proc]; simp
  have hparts0 : procParts K 0 = ∅ := by
    ext k; rw [mem_procParts]; simp
  have hProcK : Proc I K = Finset.univ := by
    ext c
    rw [mem_Proc]
    constructor
    · intro _; exact Finset.mem_univ c
    · intro _
      have hc : c ∈ Finset.univ.biUnion I := by rw [hIuniv]; exact Finset.mem_univ c
      rw [Finset.mem_biUnion] at hc
      obtain ⟨k, -, hck⟩ := hc
      exact ⟨k, k.isLt, hck⟩
  have hProcKcard : ((Proc I K).card : ℝ) = (D : ℝ) := by rw [hProcK]; simp
  have hsumI : (∑ k : Fin K, ((I k).card : ℝ)) = (D : ℝ) := by
    have h1 : (∑ k : Fin K, (I k).card) = D := by
      rw [← Finset.card_biUnion (h := fun i _ j _ hij => hIdisj i j hij), hIuniv]
      simp
    exact_mod_cast h1
  have hEdgeSet : ∀ e ∈ 𝓗'.edgeSet, ∃ k : Fin K, e ∈ (P.part k).edgeSet := by
    intro e he
    rcases he with he | ⟨v, rfl, hv⟩
    · obtain ⟨k, hk, -⟩ := P.edges_cover e he
      exact ⟨k, Or.inl hk⟩
    · have h1 : 0 < (∑ k : Fin K, (P.part k).singles v) := by
        rw [singles_parts_sum P v]; omega
      have h2 : ∃ k : Fin K, 0 < (P.part k).singles v := by
        by_contra hcon
        push_neg at hcon
        have h3 : (∑ k : Fin K, (P.part k).singles v) = 0 :=
          Finset.sum_eq_zero (fun k _ => Nat.le_zero.mp (hcon k))
        omega
      obtain ⟨k, hk⟩ := h2
      exact ⟨k, Or.inr ⟨v, rfl, hk⟩⟩
  have hSingles : ∀ w : Fin n, (∑ k : Fin K, ((P.part k).singles w : ℝ))
      = (𝓗'.singles w : ℝ) := by
    intro w
    exact_mod_cast singles_parts_sum P w
  -- ================= the invariant step =================
  have step : ∀ (j : ℕ) (hj : j < K) (Nf : Fin D → Set (Set (Fin n))),
      Inv 𝓗 𝓗' R U S M I P κ γp ε j Nf →
      ∃ Nf' : Fin D → Set (Set (Fin n)), Inv 𝓗 𝓗' R U S M I P κ γp ε (j + 1) Nf' :=
    asmStep (𝓥 := 𝓥) habs hU hU𝓥 huniv𝓥 hSsub hC1 hlinH hle hlin' hout hsize hMmatch
      hMdisj hMout hMR hMsz hMint hpar hint hcross P I hIcard hIdisj hIuniv hKslide hpartdeg
      hseed hint' hPMS
  have base : Inv 𝓗 𝓗' R U S M I P κ γp ε 0 M := by
    have h1 : ∀ c : Fin D, c ∉ Proc I 0 := by
      intro c hc; rw [hProc0] at hc; exact absurd hc (Finset.notMem_empty c)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c _; rfl
    · intro c hc; exact absurd hc (h1 c)
    · exact hMdisj
    · intro w; rw [hProc0]; simp
    · intro k hk w; rw [hparts0] at hk; exact absurd hk (Finset.notMem_empty k)
    · refine ⟨?_, ?_⟩
      · intro _
        refine ⟨?_, ?_, ?_⟩
        · intro u _
          simp [hProc0]
        · intro c hc; rw [hProc0] at hc; exact absurd hc (Finset.notMem_empty c)
        · intro c hc; rw [hProc0] at hc; exact absurd hc (Finset.notMem_empty c)
      · intro _ c hc; exact absurd hc (h1 c)
    · intro w
      have h2 : asmSinglesSum 𝓗' P 0 w = 0 := by
        rw [asmSinglesSum, hparts0]; simp
      rw [h2]
      have h3 : (((Proc I 0).filter (fun c => ({w} : Set (Fin n)) ∈ M c ∧
          ({w} : Set (Fin n)) ∉ M c)).card : ℝ) = 0 := by
        rw [hProc0]; simp
      rw [h3]
  have main : ∀ j : ℕ, j ≤ K → ∃ Nf : Fin D → Set (Set (Fin n)),
      Inv 𝓗 𝓗' R U S M I P κ γp ε j Nf := by
    intro j
    induction j with
    | zero => intro _; exact ⟨M, base⟩
    | succ j ih =>
      intro hj
      obtain ⟨Nf, hNf⟩ := ih (Nat.le_of_lt (Nat.lt_of_succ_le hj))
      exact step j (Nat.lt_of_succ_le hj) Nf hNf
  obtain ⟨Nf, hNf⟩ := main K le_rfl
  obtain ⟨hInv_a, hInv_b, hInv_c, hInv_d, hInv_e, hInv_f, hInv_g⟩ := hNf
  obtain ⟨hInv_fA, hInv_fB⟩ := hInv_f
  have hmemProc : ∀ i : Fin D, i ∈ Proc I K := by
    intro i; rw [hProcK]; exact Finset.mem_univ i
  refine ⟨Nf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hInv_b i (hmemProc i)).1
  · intro i
    exact (hInv_b i (hmemProc i)).2.1
  · intro i e he hne
    rcases (hInv_b i (hmemProc i)).2.2 e he hne with hR | ⟨k, hk, hik, hek⟩
    · exact Or.inr hR
    · exact Or.inl (MultiHypergraph.edgeSet_mono (P.le k) hek)
  · intro i j hij
    exact hInv_c i j hij
  · intro w
    have h1 := hInv_d w
    have h2 : (⋃ c ∈ Proc I K, Nf c) = (⋃ i : Fin D, Nf i) := by
      ext x
      simp only [Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨c, -, hx⟩; exact ⟨c, hx⟩
      · rintro ⟨c, hx⟩; exact ⟨c, hmemProc c, hx⟩
    rw [h2] at h1
    have h3 : (γp + 2 * κ) * ((Proc I K).card : ℝ) ≤ γ * (D : ℝ) := by
      rw [hProcKcard]
      exact mul_le_mul_of_nonneg_right hpar.hγpγup (Nat.cast_nonneg D)
    linarith
  · intro w
    have h2 : (⋃ c ∈ Proc I K, Nf c) = (⋃ i : Fin D, Nf i) := by
      ext x
      simp only [Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨c, -, hx⟩; exact ⟨c, hx⟩
      · rintro ⟨c, hx⟩; exact ⟨c, hmemProc c, hx⟩
    set S : Fin K → Set (Set (Fin n)) :=
      fun k => {e ∈ (P.part k).edgeSet | w ∈ e} \ (⋃ c ∈ I k, Nf c) with hS
    have hsub : ({e ∈ 𝓗'.edgeSet | w ∈ e} \ (⋃ i : Fin D, Nf i)) ⊆ ⋃ k, S k := by
      intro e he
      obtain ⟨⟨heE, hwe⟩, heU⟩ := he
      obtain ⟨k, hk⟩ := hEdgeSet e heE
      refine Set.mem_iUnion.mpr ⟨k, ⟨⟨hk, hwe⟩, ?_⟩⟩
      rintro hc
      rw [Set.mem_iUnion] at hc
      obtain ⟨c, hcN⟩ := hc
      rw [Set.mem_iUnion] at hcN
      obtain ⟨-, hcN⟩ := hcN
      exact heU (by rw [← h2]; exact Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hmemProc c, hcN⟩⟩)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : (((⋃ k : Fin K, S k).ncard : ℕ) : ℝ)
        ≤ ∑ k : Fin K, ((γp + 2 * κ) * ((I k).card : ℝ)) :=
      ncard_iUnion_le_sumR S _ (fun k => hInv_e k (mem_procParts.mpr k.isLt) w)
    have h3 : (∑ k : Fin K, ((γp + 2 * κ) * ((I k).card : ℝ)))
        = (γp + 2 * κ) * (D : ℝ) := by
      rw [← Finset.mul_sum, hsumI]
    have h4 : (γp + 2 * κ) * (D : ℝ) ≤ γ * (D : ℝ) :=
      mul_le_mul_of_nonneg_right hpar.hγpγup (Nat.cast_nonneg D)
    have h5 : (((⋃ k : Fin K, S k).ncard : ℕ) : ℝ) ≤ γ * (D : ℝ) := by linarith
    have h6 : ((({e ∈ 𝓗'.edgeSet | w ∈ e} \ (⋃ i : Fin D, Nf i)).ncard : ℕ) : ℝ)
        ≤ (((⋃ k : Fin K, S k).ncard : ℕ) : ℝ) := by exact_mod_cast h1
    exact h6.trans h5
  · intro hsmall i
    exact hInv_fB (not_lt.mpr hsmall) i (hmemProc i)
  · intro hbig
    obtain ⟨h1, h2, h3⟩ := hInv_fA hbig
    refine ⟨?_, ?_, ?_⟩
    · intro u hu
      have hset : ({c ∈ Proc I K | u ∈ famVert (Nf c)} : Set (Fin D))
          = {i : Fin D | u ∈ famVert (Nf i)} := by
        ext c; simp [hProcK]
      have h5 := h1 u hu
      rw [hset] at h5
      rw [hProcKcard] at h5
      simpa using h5
    · intro i
      exact h2 i (hmemProc i)
    · intro i
      exact h3 i (hmemProc i)
  · intro w
    have h1 := hInv_g w
    rw [asmSinglesSum_eq P w] at h1
    have hset : ((Finset.univ.filter (fun c : Fin D => ({w} : Set (Fin n)) ∈ Nf c ∧
        ({w} : Set (Fin n)) ∉ M c) : Finset (Fin D)) : Set (Fin D))
        = {i : Fin D | ({w} : Set (Fin n)) ∈ Nf i ∧ ({w} : Set (Fin n)) ∉ M i} := by
      ext c; simp
    have h3 : (Proc I K).filter (fun c => ({w} : Set (Fin n)) ∈ Nf c ∧
        ({w} : Set (Fin n)) ∉ M c) = Finset.univ.filter (fun c => ({w} : Set (Fin n)) ∈ Nf c ∧
        ({w} : Set (Fin n)) ∉ M c) := by
      ext c; simp [hProcK]
    rw [h3] at h1
    have h4 : ((Finset.univ.filter (fun c : Fin D => ({w} : Set (Fin n)) ∈ Nf c ∧
        ({w} : Set (Fin n)) ∉ M c)).card : ℝ)
        = ((({i : Fin D | ({w} : Set (Fin n)) ∈ Nf i ∧ ({w} : Set (Fin n)) ∉ M i}
            : Set (Fin D)).ncard) : ℝ) := by
      rw [← Set.ncard_coe_finset (Finset.univ.filter (fun c : Fin D =>
        ({w} : Set (Fin n)) ∈ Nf c ∧ ({w} : Set (Fin n)) ∉ M c))]
      rw [hset]
    rw [h4] at h1
    exact_mod_cast h1

end
