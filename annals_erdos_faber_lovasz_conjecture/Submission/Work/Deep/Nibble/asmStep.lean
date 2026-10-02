import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.AsmBase
import Submission.Work.Deep.Nibble.asmDefs
import Submission.Work.Deep.Nibble.asmObj
import Submission.Work.Deep.Nibble.asmHelp
import Submission.Work.Deep.Nibble.ncard_colours_singleton_le
import Submission.Work.Deep.Nibble.ncard_Redges_le_missing
import Submission.Work.Deep.Nibble.ncard_uncovered_le_unused
import Submission.Work.Deep.Nibble.ncard_miss_objVert_le
import Submission.Work.Deep.Nibble.absorbBatch_cond
import Submission.Work.Deep.Nibble.exists_objMatching

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

local notation "Hypergraph" => ErdosFaberLovaszConjecture.Hypergraph

set_option maxHeartbeats 1000000

theorem asmStep {n D r K : ℕ}
    {𝓗 𝓗' : ErdosFaberLovaszConjecture.MultiHypergraph n}
    {R : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    {𝓥 : Set (Set (Fin n))} {U S : Set (Fin n)}
    {M : Fin D → Set (Set (Fin n))} {ρ γ β ξ ε : ℝ}
    {κ γp δ βp : ℝ}
    (habs : ErdosFaberLovaszConjecture.IsAbsorber
      (ErdosFaberLovaszConjecture.incidentTwo
        (ErdosFaberLovaszConjecture.MultiHypergraph.pow2 𝓗) U) R 𝓥 ρ γ ξ)
    (hU : U = ErdosFaberLovaszConjecture.VplusTwo
      (ErdosFaberLovaszConjecture.MultiHypergraph.pow2 𝓗) (1 - ε))
    (hU𝓥 : U ∈ 𝓥) (huniv𝓥 : (Set.univ : Set (Fin n)) ∈ 𝓥)
    (hSsub : S ⊆ U)
    (hC1 : (1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ) →
      (D : ℝ) + γ * (n : ℝ) ≤ (S.ncard : ℝ))
    (hlinH : 𝓗.IsLinear) (hle : 𝓗' ≤ 𝓗) (hlin' : 𝓗'.IsLinear)
    (hout : ∀ e ∈ 𝓗'.edges, e ∉ R)
    (hsize : ∀ e ∈ 𝓗'.edges, ErdosFaberLovaszConjecture.edgeSize e ≤ r)
    (hMmatch : ∀ i, 𝓗.IsMatching (M i))
    (hMdisj : ∀ i j, i ≠ j → ErdosFaberLovaszConjecture.EdgeDisjointFam (M i) (M j))
    (hMout : ∀ i, ∀ e ∈ M i, e ∉ 𝓗'.edgeSet)
    (hMR : ∀ i, ∀ e ∈ M i, e ∉ R)
    (hMsz : ∀ i, ((ErdosFaberLovaszConjecture.famVert (M i)).ncard : ℝ) ≤ β * (D : ℝ))
    (hMint : ∀ e ∈ 𝓗'.edgeSet,
      (({i : Fin D | (e ∩ ErdosFaberLovaszConjecture.famVert (M i)).Nonempty}).ncard : ℝ)
        ≤ β * (D : ℝ))
    (hpar : ErdosFaberLovaszConjecture.AssemblyParams n (D : ℝ) β γ ε ρ ξ κ γp δ βp K)
    (hint : ErdosFaberLovaszConjecture.InternalMargins n ρ ε γp κ ξ)
    (hcross : ErdosFaberLovaszConjecture.CrossingMargins n ρ ε γp κ ξ)
    (P : ErdosFaberLovaszConjecture.EdgePartition 𝓗' K) (I : Fin K → Finset (Fin D))
    (hIcard : ∀ i, D / K ≤ (I i).card ∧ (I i).card ≤ D / K + 1)
    (hIdisj : ∀ i j, i ≠ j → Disjoint (I i) (I j))
    (hIuniv : Finset.univ.biUnion I = Finset.univ)
    (hKslide : (n : ℝ) ^ ((1 : ℝ) / 2) + 1 ≤ (D : ℝ) / (K : ℝ))
    (hpartdeg : ∀ i w, |(((P.part i).deg w : ℝ)) - ((I i).card : ℝ)| ≤ βp * ((I i).card : ℝ))
    (hseed : ∀ i c, c ∈ I i →
      ((ErdosFaberLovaszConjecture.famVert (M c)).ncard : ℝ) ≤ βp * ((I i).card : ℝ))
    (hint' : ∀ i e, e ∈ (P.part i).edgeSet →
      (({c : Fin D | c ∈ I i ∧ (e ∩ ErdosFaberLovaszConjecture.famVert (M c)).Nonempty}).ncard : ℝ)
        ≤ βp * ((I i).card : ℝ))
    (hPMS : ErdosFaberLovaszConjecture.PseudorandomMatchingAtObj n r βp κ γp) :
    ∀ (j : ℕ) (hj : j < K) (Nf : Fin D → Set (Set (Fin n))),
      Work.Deep.Nibble.Inv 𝓗 𝓗' R U S M I P κ γp ε j Nf →
      ∃ Nf' : Fin D → Set (Set (Fin n)),
        Work.Deep.Nibble.Inv 𝓗 𝓗' R U S M I P κ γp ε (j + 1) Nf' := by

  classical
  intro j hj Nf hInv
  obtain ⟨hInva, hInvb, hInvc, hInvd, hInve, hInvf, hInvg⟩ := hInv
  -- ## 1. numeric facts
  have hκ0 : 0 < κ := hpar.hκ0
  have hβp0 : 0 ≤ βp := le_of_lt hpar.hβp0
  have hβp1 : βp ≤ 1 := hpar.hβp1
  have hγp0 : 0 < γp := hpar.hγp0
  have hγp_le : γp ≤ 1 / 20000 := by
    have h1 : γp ≤ ρ / 20000 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 20000)]; linarith [hpar.hγpρ]
    linarith [h1, hint.hρ1]
  have hγp1 : γp ≤ 1 := by linarith
  have hγp100 : γp ≤ 1 / 100 := by linarith
  have hκ1 : κ ≤ 1 := by nlinarith [hpar.hκγ, hγp_le]
  have hκ16 : κ ≤ 1 / 6 := by nlinarith [hpar.hκγ, hγp_le]
  have hβp10 : βp ≤ 1 / 10 := by nlinarith [hpar.hβpκ, hκ1]
  have hγρ_le : γp * ρ ≤ 1 / 20000 := by
    nlinarith [hγp_le, hγp0, hint.hρ, hint.hρ1]
  have hn8 : (8:ℝ) ≤ (n:ℝ) := by
    have h1 : (2000:ℝ) ≤ γp * ρ * (n:ℝ) := hpar.hγpbig
    have h2 : (0:ℝ) < γp * ρ := by nlinarith [hγp0, hint.hρ]
    by_contra hcon
    have h5 : (n:ℝ) < 8 := not_le.mp hcon
    have h6 : γp * ρ * (n:ℝ) < γp * ρ * 8 := mul_lt_mul_of_pos_left h5 h2
    have h7 : γp * ρ * 8 ≤ (1/20000) * 8 := mul_le_mul_of_nonneg_right hγρ_le (by norm_num)
    linarith
  have hn8n : 8 ≤ n := by exact_mod_cast hn8
  have hn6 : (6:ℝ) ≤ (n:ℝ) := by linarith
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by linarith
  have hn0 : (0:ℝ) < (n:ℝ) := by linarith
  have hlog2 : (2:ℝ) ≤ Real.log (n:ℝ) := by
    have h1 : Real.log 8 ≤ Real.log (n:ℝ) := Real.log_le_log (by norm_num) hn8
    have h2 : Real.log (8:ℝ) = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have h3 : (0.69:ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
    linarith
  have hpow : (n:ℝ)^(2:ℝ) ≤ (n:ℝ)^(Real.log (n:ℝ)) := by
    have h1 : (1:ℝ) < (n:ℝ) := by linarith
    exact (Real.rpow_le_rpow_left_iff h1).mpr hlog2
  have hDnR : (D:ℝ) < (n:ℝ) := by
    have h := hpar.hKround
    have h1 : (0:ℝ) < (n:ℝ) - (D:ℝ) := by
      by_contra hcon
      have : κ * ((n:ℝ) - (D:ℝ)) ≤ 0 := by nlinarith [hκ0, not_lt.mp hcon]
      linarith
    linarith
  have hDle : (D:ℝ) ≤ (n:ℝ) := le_of_lt hDnR
  have hKpos : 0 < K := Nat.lt_of_lt_of_le (by norm_num) hpar.hK
  have hKposR : (0:ℝ) < (K:ℝ) := by exact_mod_cast hKpos
  have hκn2 : 2 ≤ κ * (n:ℝ) := by
    have h1 := hpar.hKfloor
    have h2 : κ * (D:ℝ) ≤ κ * (n:ℝ) := mul_le_mul_of_nonneg_left hDle (le_of_lt hκ0)
    have h3 : (1:ℝ) ≤ (n:ℝ)^((1:ℝ)/2) := Real.one_le_rpow hn1 (by norm_num)
    linarith
  have hκn1 : 1 ≤ κ * (n:ℝ) := by linarith
  have hκn_le : κ * (n:ℝ) + 1 ≤ (n:ℝ) := by nlinarith [hκn2, hn6, hκ16]
  -- ## 2. the slack constant and the absorption margins
  set κa : ℝ := slackκ κ βp n with hκadef
  have hintA : InternalMargins n ρ ε γp κa ξ := by
    rw [hκadef]; exact internalMargins_slack hκn2 hβp0 hβp10 hint hpar.hκγ2'
  have hcrossA : CrossingMargins n ρ ε γp κa ξ := by
    rw [hκadef]; exact crossingMargins_slack hκn2 hβp0 hβp10 hint hcross
  -- ## 3. the remaining reservoir and defect set
  set Rcur : Hypergraph (Fin n) := RcurOf R I Nf j with hRcurdef
  set Scur : Set (Fin n) := ScurOf S U I Nf j with hScurdef
  have hRcurSub : Rcur ⊆ R := by rw [hRcurdef]; exact RcurOf_subset R I Nf j
  have hScurSub : Scur ⊆ S := by rw [hScurdef]; exact ScurOf_subset S U I Nf j
  have hR2 : ∀ e ∈ R, edgeSize e = 2 :=
    fun e he => edgeSize_two_of_mem_incidentTwo (habs.1 he)
  have hR2Rcur : ∀ e ∈ Rcur, edgeSize e = 2 := fun e he => hR2 e (hRcurSub he)
  -- ## 4. the block and the size of the part
  have hblock_le : ((I ⟨j,hj⟩).card : ℝ) ≤ κ * (n:ℝ) + 1 := by
    have h1 := (hIcard ⟨j,hj⟩).2
    have h2 : ((D / K : ℕ) : ℝ) ≤ κ * (n:ℝ) := by
      have h3 : (D:ℝ) ≤ κ * (n:ℝ) * (K:ℝ) := hpar.hKup
      have h4 : (D:ℝ) / (K:ℝ) ≤ κ * (n:ℝ) := by rw [div_le_iff₀ hKposR]; linarith
      have h5 : ((D / K : ℕ) : ℝ) ≤ (D:ℝ)/(K:ℝ) := Nat.cast_div_le
      linarith
    have h6 : ((I ⟨j,hj⟩).card : ℝ) ≤ ((D / K : ℕ) : ℝ) + 1 := by exact_mod_cast h1
    linarith
  have hblock_le_n : ((I ⟨j,hj⟩).card : ℝ) ≤ (n:ℝ) := by linarith [hblock_le, hκn_le]
  have hblock_low : (n:ℝ)^((1:ℝ)/2) ≤ ((I ⟨j,hj⟩).card : ℝ) := by
    have hlt : D < (D / K + 1) * K := (Nat.div_lt_iff_lt_mul hKpos).mp (Nat.lt_succ_self _)
    have hcast : (D:ℝ)/(K:ℝ) < ((D / K : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hKposR]
      have h2 : ((D:ℕ):ℝ) < (((D / K + 1) * K : ℕ):ℝ) := by exact_mod_cast hlt
      push_cast at h2; linarith
    have h3 : ((D / K : ℕ) : ℝ) ≤ ((I ⟨j,hj⟩).card : ℝ) := by exact_mod_cast (hIcard ⟨j,hj⟩).1
    linarith [hKslide]
  have hκa_le : κ + γp * (βp * ((I ⟨j,hj⟩).card : ℝ)) / (n:ℝ) ≤ κa := by
    have h1 : γp * (βp * ((I ⟨j,hj⟩).card : ℝ)) ≤ γp * (βp * (κ * (n:ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hblock_le hβp0) (le_of_lt hγp0)
    have h1' : γp * (βp * ((I ⟨j,hj⟩).card : ℝ)) / (n:ℝ)
        ≤ γp * (βp * (κ * (n:ℝ) + 1)) / (n:ℝ) := div_le_div_of_nonneg_right h1 (le_of_lt hn0)
    have h2 : γp * (βp * (κ * (n:ℝ) + 1)) / (n:ℝ) ≤ γp * βp * (κ + 1/(n:ℝ)) := by
      rw [div_le_iff₀ hn0]
      have he : γp * βp * (κ + 1/(n:ℝ)) * (n:ℝ) = γp * (βp * (κ * (n:ℝ) + 1)) := by
        field_simp
      rw [he]
    have h3 : γp * βp * (κ + 1/(n:ℝ)) ≤ κ * βp + 1/(n:ℝ) := by
      have h4 : γp * βp ≤ βp := by nlinarith [hγp1, hβp0]
      have h5 : γp * βp ≤ 1 := by nlinarith [hγp1, hβp1, hβp0]
      have h6 : γp * βp * κ ≤ κ * βp := by nlinarith [hγp1, hβp0, hκ0]
      have h7 : γp * βp * (1/(n:ℝ)) ≤ 1/(n:ℝ) := by
        have := mul_le_mul_of_nonneg_right h5 (le_of_lt (by positivity : (0:ℝ) < 1/(n:ℝ)))
        rwa [one_mul] at this
      nlinarith [h6, h7]
    have h8 : κ + (κ * βp + 1/(n:ℝ)) = κ * (1 + βp) + 1/(n:ℝ) := by ring
    rw [hκadef, slackκ]
    linarith [h1', h2, h3, h8]
  have hKbatch : ((I ⟨j,hj⟩).card : ℝ) ≤ κa * (n:ℝ) := by
    rw [hκadef, slackκ]
    have h2 : (κ * (1 + βp) + 1 / (n:ℝ)) * (n:ℝ) = κ * (1 + βp) * (n:ℝ) + 1 := by
      field_simp
    rw [h2]
    nlinarith [hblock_le, hκ0, hβp0]
  -- ## 5. the two pseudorandomness families handed to the deep input
  have habsCard : (absorberFam Rcur U).ncard ≤ 2 * n := by
    have h1 : absorberFam Rcur U ⊆
        ((fun u : Fin n => nbrs Rcur u ∩ U) '' (Set.univ : Set (Fin n))) ∪
        ((fun u : Fin n => nbrs Rcur u \ U) '' (Set.univ : Set (Fin n))) := by
      rintro X (⟨u, rfl⟩ | ⟨u, rfl⟩)
      · exact Or.inl ⟨u, Set.mem_univ u, rfl⟩
      · exact Or.inr ⟨u, Set.mem_univ u, rfl⟩
    have h2 : (((fun u : Fin n => nbrs Rcur u ∩ U) '' (Set.univ : Set (Fin n))) ∪
        ((fun u : Fin n => nbrs Rcur u \ U) '' (Set.univ : Set (Fin n)))).ncard ≤ 2 * n := by
      have h3 := Set.ncard_union_le
        ((fun u : Fin n => nbrs Rcur u ∩ U) '' (Set.univ : Set (Fin n)))
        ((fun u : Fin n => nbrs Rcur u \ U) '' (Set.univ : Set (Fin n)))
      have h4 : ((fun u : Fin n => nbrs Rcur u ∩ U) '' (Set.univ : Set (Fin n))).ncard ≤ n := by
        have h := Set.ncard_image_le (s := (Set.univ : Set (Fin n)))
          (f := fun u : Fin n => nbrs Rcur u ∩ U)
        rwa [Set.ncard_univ, Nat.card_fin] at h
      have h5 : ((fun u : Fin n => nbrs Rcur u \ U) '' (Set.univ : Set (Fin n))).ncard ≤ n := by
        have h := Set.ncard_image_le (s := (Set.univ : Set (Fin n)))
          (f := fun u : Fin n => nbrs Rcur u \ U)
        rwa [Set.ncard_univ, Nat.card_fin] at h
      omega
    exact le_trans (Set.ncard_le_ncard h1) h2
  have habsorbFamCard : (absorbFam Rcur U Scur).ncard ≤ 2 * n + 3 := by
    have h1 : absorbFam Rcur U Scur ⊆ absorberFam Rcur U ∪ ({U, Scur, ∅} : Set (Set (Fin n))) := by
      intro x hx
      rw [absorbFam] at hx
      exact hx
    have h3 : ({U, Scur, ∅} : Set (Set (Fin n))).ncard ≤ 3 := by
      have h4 : ({U, Scur, ∅} : Set (Set (Fin n))) = insert U (insert Scur ({∅} : Set (Set (Fin n)))) := rfl
      rw [h4]
      refine le_trans (Set.ncard_insert_le U _) ?_
      refine le_trans (Nat.add_le_add_right (Set.ncard_insert_le Scur ({∅} : Set (Set (Fin n)))) 1) ?_
      rw [Set.ncard_singleton]
    have h2 : (absorberFam Rcur U ∪ ({U, Scur, ∅} : Set (Set (Fin n)))).ncard ≤ 2 * n + 3 := by
      have h5 := Set.ncard_union_le (absorberFam Rcur U) ({U, Scur, ∅} : Set (Set (Fin n)))
      omega
    exact le_trans (Set.ncard_le_ncard h1) h2
  have hshiftCard : (shiftFam I M ⟨j,hj⟩ (absorbFam Rcur U Scur)).ncard
      ≤ (absorbFam Rcur U Scur).ncard * (I ⟨j,hj⟩).card := by
    have h1 : shiftFam I M ⟨j,hj⟩ (absorbFam Rcur U Scur) ⊆
        (fun p : Set (Fin n) × Fin D => p.1 \ famVert (M p.2)) ''
          ((absorbFam Rcur U Scur) ×ˢ ((I ⟨j,hj⟩ : Finset (Fin D)) : Set (Fin D))) := by
      rintro A ⟨X, hX, c, hc, rfl⟩
      exact ⟨(X, c), ⟨hX, Finset.mem_coe.mpr hc⟩, rfl⟩
    calc (shiftFam I M ⟨j,hj⟩ (absorbFam Rcur U Scur)).ncard
        ≤ ((absorbFam Rcur U Scur) ×ˢ ((I ⟨j,hj⟩ : Finset (Fin D)) : Set (Fin D))).ncard :=
          le_trans (Set.ncard_le_ncard h1) (Set.ncard_image_le)
      _ = (absorbFam Rcur U Scur).ncard * (I ⟨j,hj⟩).card := by
          rw [Set.ncard_prod, Set.ncard_coe_finset]
  have hfamV : ((shiftFam I M ⟨j,hj⟩ (absorbFam Rcur U Scur)).ncard : ℝ)
      ≤ (n:ℝ) ^ (Real.log (n:ℝ)) := by
    have h1 : ((shiftFam I M ⟨j,hj⟩ (absorbFam Rcur U Scur)).ncard : ℝ)
        ≤ (2 * (n:ℝ) + 3) * (κ * (n:ℝ) + 1) := by
      have h2 : ((shiftFam I M ⟨j,hj⟩ (absorbFam Rcur U Scur)).ncard : ℝ)
          ≤ ((absorbFam Rcur U Scur).ncard : ℝ) * ((I ⟨j,hj⟩).card : ℝ) := by
        exact_mod_cast hshiftCard
      have h3 : ((absorbFam Rcur U Scur).ncard : ℝ) ≤ 2 * (n:ℝ) + 3 := by exact_mod_cast habsorbFamCard
      have h4 : ((I ⟨j,hj⟩).card : ℝ) ≤ κ * (n:ℝ) + 1 := hblock_le
      have h6 : (0:ℝ) ≤ ((I ⟨j,hj⟩).card : ℝ) := Nat.cast_nonneg _
      have h7 : (0:ℝ) ≤ 2 * (n:ℝ) + 3 := by linarith
      have h8 : ((absorbFam Rcur U Scur).ncard : ℝ) * ((I ⟨j,hj⟩).card : ℝ)
          ≤ (2 * (n:ℝ) + 3) * (κ * (n:ℝ) + 1) := mul_le_mul h3 h4 h6 h7
      linarith [h2, h8]
    have h2 : (2 * (n:ℝ) + 3) * (κ * (n:ℝ) + 1) ≤ (n:ℝ)^(2:ℝ) := by
      have ha : 2 * (n:ℝ) + 3 ≤ 3 * (n:ℝ) := by linarith
      have hb : κ * (n:ℝ) + 1 ≤ (n:ℝ)/3 := by nlinarith [hκ16, hn6]
      have hc : (0:ℝ) ≤ κ * (n:ℝ) + 1 := by linarith [hκn1]
      have hd : (0:ℝ) ≤ 3 * (n:ℝ) := by linarith
      have hh := mul_le_mul ha hb hc hd
      rw [Real.rpow_two]
      refine le_trans hh (le_of_eq ?_)
      ring
    exact le_trans h1 (le_trans h2 hpow)
  have hfamE : (({objThrough (P.part ⟨j,hj⟩) w | w : Fin n} :
      Set (Set (EdgeObj (P.part ⟨j,hj⟩)))).ncard : ℝ)
      ≤ (n : ℝ) ^ (Real.log (n : ℝ)) := by
    have h1 : ({objThrough (P.part ⟨j,hj⟩) w | w : Fin n} :
        Set (Set (EdgeObj (P.part ⟨j,hj⟩)))).ncard ≤ n := by
      have h := Set.ncard_image_le (s := (Set.univ : Set (Fin n)))
        (f := fun w : Fin n => objThrough (P.part ⟨j,hj⟩) w)
      rw [Set.ncard_univ, Nat.card_fin] at h
      rwa [Set.image_univ] at h
    have h2 : (n:ℝ) ≤ (n:ℝ)^(Real.log (n:ℝ)) := by
      have h3 : (1:ℝ) < (n:ℝ) := by linarith
      calc (n:ℝ) = (n:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
        _ ≤ (n:ℝ)^(Real.log (n:ℝ)) := (Real.rpow_le_rpow_left_iff h3).mpr (by linarith)
    have h4 : (({objThrough (P.part ⟨j,hj⟩) w | w : Fin n} :
        Set (Set (EdgeObj (P.part ⟨j,hj⟩)))).ncard : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast h1
    linarith
  -- ## 6. the pseudorandom matchings of the deep input
  obtain ⟨Nobj, hNobjMatch, hNobjDisj, hNobjAvoid, hNobjPr, hNobjLeft⟩ :=
    exists_objMatching (P := P) (I := I) (k := ⟨j,hj⟩) (M := M)
      (R := R) (Rcur := Rcur) (U := U) (S := Scur)
      hPMS hlinH hle hlin' (hpartdeg ⟨j,hj⟩) hsize hMmatch hMout hMdisj
      (hseed ⟨j,hj⟩) (hint' ⟨j,hj⟩) hblock_low hblock_le_n hfamV hfamE
  -- ## 7. the batch of colours of this step
  set batch : Fin (I ⟨j,hj⟩).card → Set (Set (Fin n)) :=
    fun i => blockSeed I M ⟨j,hj⟩ i ∪ objFam (Nobj i) with hbatchdef
  have hBatchMat : ∀ i, MultiHypergraph.IsMatching 𝓗 (batch i) := by
    intro i
    rw [hbatchdef]
    refine MultiHypergraph.IsMatching.union ?_ ?_ ?_
    · rw [blockSeed_apply]; exact hMmatch _
    · refine ⟨?_, (isMatching_objFam (hNobjMatch i)).2⟩
      intro e he
      exact MultiHypergraph.edgeSet_mono hle
        (MultiHypergraph.edgeSet_mono (P.le ⟨j,hj⟩) (objFam_subset_edgeSet (Nobj i) he))
    · rw [famVert_objFam]
      exact (hNobjAvoid i).symm
  have hBatchDisj : ∀ i i', i ≠ i' → EdgeDisjointFam (batch i) (batch i') := by
    intro i i' hii'
    rw [hbatchdef]
    refine edgeDisjointFam_union ?_ ?_ ?_ ?_
    · rw [blockSeed_apply, blockSeed_apply]
      exact hMdisj _ _ (fun h => hii' (blockColour_injective I ⟨j,hj⟩ h))
    · rw [EdgeDisjointFam, Set.disjoint_left]
      intro e he he'
      simp only [nonsing, Set.mem_setOf_eq] at he he'
      rw [blockSeed_apply] at he
      exact hMout _ e he.1
        (MultiHypergraph.edgeSet_mono (P.le ⟨j,hj⟩) (objFam_subset_edgeSet (Nobj i') he'.1))
    · rw [EdgeDisjointFam, Set.disjoint_left]
      intro e he he'
      simp only [nonsing, Set.mem_setOf_eq] at he he'
      rw [blockSeed_apply] at he'
      exact hMout _ e he'.1
        (MultiHypergraph.edgeSet_mono (P.le ⟨j,hj⟩) (objFam_subset_edgeSet (Nobj i) he.1))
    · exact edgeDisjointFam_objFam (i := i) (j := i') hNobjDisj hii'
  have hBatchNRcur : ∀ i, ∀ e ∈ batch i, e ∉ Rcur := by
    intro i e he
    have he' : e ∈ blockSeed I M ⟨j,hj⟩ i ∪ objFam (Nobj i) := he
    rcases he' with he | he
    · rw [blockSeed_apply] at he
      exact fun h => hMR _ e he (hRcurSub h)
    · intro hcon
      have hE : e ∈ 𝓗'.edgeSet :=
        MultiHypergraph.edgeSet_mono (P.le ⟨j,hj⟩) (objFam_subset_edgeSet (Nobj i) he)
      exact (edgeSet_not_mem_of_out hout hR2 e hE) (hRcurSub hcon)
  have hBatchR : ∀ i, ∀ e ∈ batch i, e ∉ R := by
    intro i e he
    have he' : e ∈ blockSeed I M ⟨j,hj⟩ i ∪ objFam (Nobj i) := he
    rcases he' with he' | he'
    · rw [blockSeed_apply] at he'
      exact hMR _ e he'
    · exact edgeSet_not_mem_of_out hout hR2 e
        (MultiHypergraph.edgeSet_mono (P.le ⟨j,hj⟩) (objFam_subset_edgeSet (Nobj i) he'))
  have hBatchPseudo : ∀ i, PseudoRandomFam (batch i) (absorbFam Rcur U Scur) γp κa := by
    intro i
    have hseed_i : ((famVert (M (blockColour I ⟨j,hj⟩ i))).ncard : ℝ)
        ≤ βp * ((I ⟨j,hj⟩).card : ℝ) := hseed ⟨j,hj⟩ _ (blockColour_mem I ⟨j,hj⟩ i)
    have hsub : ∀ X ∈ absorbFam Rcur U Scur,
        X \ famVert (M (blockColour I ⟨j,hj⟩ i)) ∈ shiftFam I M ⟨j,hj⟩ (absorbFam Rcur U Scur) :=
      fun X hX => ⟨X, hX, blockColour I ⟨j,hj⟩ i, blockColour_mem I ⟨j,hj⟩ i, rfl⟩
    have hres := pseudoRandom_union (n := n) (𝓜 := P.part ⟨j,hj⟩)
      (M := M) (Nobj := Nobj i) (base := absorbFam Rcur U Scur)
      (𝓕V := shiftFam I M ⟨j,hj⟩ (absorbFam Rcur U Scur)) (γp := γp) (κ := κ)
      (σ := βp * ((I ⟨j,hj⟩).card : ℝ))
      (by linarith : 1 ≤ n) (blockColour I ⟨j,hj⟩ i) (le_of_lt hγp0)
      (mul_nonneg hβp0 (Nat.cast_nonneg _)) hsub (hNobjPr i) hseed_i
    change PseudoRandomFam (M (blockColour I ⟨j,hj⟩ i) ∪ objFam (Nobj i))
      (absorbFam Rcur U Scur) γp κa
    exact PseudoRandomFam.mono_kappa hres hκa_le
  -- ## 8. the shrinking absorber and defect set
  have hRcurAbs : IsAbsorber (incidentTwo (MultiHypergraph.pow2 𝓗) U) Rcur 𝓥 ρ (10 * γp) ξ := by
    have hdel := habs.delete (α := γ) hRcurSub ?_
    · exact hdel.mono_gamma (by linarith [hpar.hγpγ])
    · intro v
      have hR2' : ∀ e ∈ R \ Rcur, edgeSize e = 2 := fun e he => hR2 e he.1
      rw [degAt_eq_ncard_edges (R \ Rcur) hR2' v]
      have hRcurEq : R \ Rcur = R ∩ (⋃ c ∈ Proc I j, Nf c) := by
        ext e
        constructor
        · intro he
          have hZ : e ∈ (⋃ c ∈ Proc I j, Nf c) := by
            by_contra hcon
            exact he.2 (by
              rw [hRcurdef, mem_RcurOf]
              exact ⟨he.1, fun c hc hcn =>
                hcon (Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hc, hcn⟩⟩)⟩)
          exact ⟨he.1, hZ⟩
        · rintro ⟨heR, heU⟩
          refine ⟨heR, ?_⟩
          intro hcon
          rw [hRcurdef, mem_RcurOf] at hcon
          obtain ⟨c, hcU⟩ := Set.mem_iUnion.mp heU
          obtain ⟨hc, hcn⟩ := Set.mem_iUnion.mp hcU
          exact hcon.2 c hc hcn
      have hset : ({e ∈ R \ Rcur | v ∈ e} : Set (Set (Fin n)))
          = ({e ∈ R | v ∈ e} : Set (Set (Fin n))) ∩ (⋃ c ∈ Proc I j, Nf c) := by
        rw [hRcurEq]
        ext e
        constructor
        · rintro ⟨⟨heR, heU⟩, hve⟩
          exact ⟨⟨heR, hve⟩, heU⟩
        · rintro ⟨⟨heR, hve⟩, heU⟩
          exact ⟨⟨heR, heU⟩, hve⟩
      rw [hset]
      have hproc : ((Proc I j).card : ℝ) ≤ (D:ℝ) := by
        have h3 : (Proc I j).card ≤ D := by
          have hh := Finset.card_le_card (Finset.subset_univ (Proc I j))
          simpa using hh
        exact_mod_cast h3
      have hprocD : ((Proc I j).card : ℝ) ≤ (n:ℝ) := le_trans hproc hDle
      have hγ : γp + 2 * κ ≤ γ := hpar.hγpγup
      have h1 := hInvd v
      have h2 : (0:ℝ) ≤ ((Proc I j).card : ℝ) := Nat.cast_nonneg _
      nlinarith [h1, hγ, hprocD, hκ0, hγp0]
  have hScur_le : (1 - 2 * ε) * (n:ℝ) < (U.ncard : ℝ) → γp * (n:ℝ) ≤ (Scur.ncard : ℝ) := by
    intro hbig
    set Z : Set (Fin n) := ⋃ c ∈ Proc I j, (U \ famVert (Nf c)) with hZ
    have hScurEq : Scur = S \ Z := by
      rw [hScurdef]
      rw [hZ]
      rfl
    have hZle : Z.ncard ≤ (Proc I j).card := by
      rw [hZ]
      refine ncard_biUnion_le_card (Proc I j) (fun c => U \ famVert (Nf c)) ?_
      intro c hc
      exact (hInvf.1 hbig).2.2 c hc
    have hZleR : (Z.ncard : ℝ) ≤ (D:ℝ) := by
      have h1 : ((Z.ncard : ℕ) : ℝ) ≤ ((Proc I j).card : ℝ) := by exact_mod_cast hZle
      have h2 : ((Proc I j).card : ℝ) ≤ (D:ℝ) := by
        have h3 : (Proc I j).card ≤ D := by
          have hh := Finset.card_le_card (Finset.subset_univ (Proc I j))
          simpa using hh
        exact_mod_cast h3
      linarith
    have hcard1 : (S.ncard : ℝ) - (Z.ncard : ℝ) ≤ (Scur.ncard : ℝ) := by
      have hScurEq2 : Scur = S \ (S ∩ Z) := by
        rw [hScurEq]
        ext x
        constructor
        · rintro ⟨hxS, hxZ⟩
          exact ⟨hxS, fun hcon => hxZ hcon.2⟩
        · rintro ⟨hxS, hxnot⟩
          exact ⟨hxS, fun hxZ => hxnot ⟨hxS, hxZ⟩⟩
      rw [hScurEq2]
      have hsub : S ∩ Z ⊆ S := Set.inter_subset_left
      have hle : (S ∩ Z).ncard ≤ S.ncard := Set.ncard_le_ncard hsub
      rw [Set.ncard_sdiff hsub, Nat.cast_sub hle]
      have h3 : ((S ∩ Z).ncard : ℝ) ≤ (Z.ncard : ℝ) := by
        exact_mod_cast (Set.ncard_le_ncard (Set.inter_subset_right : S ∩ Z ⊆ Z))
      linarith
    have hC1' := hC1 hbig
    have hγpγ : γp ≤ γ := by linarith [hpar.hγpγup, le_of_lt hκ0]
    nlinarith [hcard1, hZleR, hC1', hγpγ, hγp0, hn0]
  -- ## 9. the absorption
  have hUdeg : ∀ u ∈ U, (1 - ε) * (n:ℝ)
      ≤ (degAt (incidentTwo (MultiHypergraph.pow2 𝓗) U) u : ℝ) := by
    intro u hu
    have h1 : (1 - ε) * (n:ℝ) ≤ (degAt (MultiHypergraph.pow2 𝓗) u : ℝ) := by
      have hh := hu
      rw [hU] at hh
      exact hh
    rw [degAt_incidentTwo_pow2 𝓗 hu]
    exact h1
  have hScurU : Scur ⊆ U := fun x hx => hSsub (hScurSub hx)
  obtain ⟨Nabs, hAbsSub, hAbsNew, hAbsMat, hAbsDisj, hAbsCov, hAbsNear⟩ :=
    absorbBatch_cond (𝓗 := 𝓗) (R := R) (Rcur := Rcur) (𝓥 := 𝓥) (U := U) (S := Scur)
      (ρ := ρ) (ε := ε) (γp := γp) (κa := κa) (ξ := ξ)
      hintA hcrossA hR2Rcur hRcurAbs hU𝓥 hUdeg hγp100 hScurU hScur_le batch hBatchMat hBatchDisj
      hBatchNRcur hBatchPseudo hKbatch
  -- ## 10. the new family of colour classes
  set Nf' : Fin D → Set (Set (Fin n)) := extend Nf I ⟨j,hj⟩ Nabs with hNf'def
  have hNfk : ∀ (c : Fin D) (h : c ∈ I ⟨j,hj⟩),
      Nf' c = Nabs ((blockEquiv I ⟨j,hj⟩).symm ⟨c, h⟩) := by
    intro c h
    rw [hNf'def]; exact extend_of_mem h
  have hNfn : ∀ (c : Fin D) (h : c ∉ I ⟨j,hj⟩), Nf' c = Nf c := by
    intro c h
    rw [hNf'def]; exact extend_of_not_mem h
  have hNabs_decomp : ∀ (c : Fin D) (hc : c ∈ I ⟨j,hj⟩) (f : Set (Fin n)),
      f ∈ Nabs ((blockEquiv I ⟨j,hj⟩).symm ⟨c, hc⟩) →
        f ∈ M c ∨ f ∈ Rcur ∨ f ∈ objFam (Nobj ((blockEquiv I ⟨j,hj⟩).symm ⟨c, hc⟩)) := by
    intro c hc f hf
    set i := (blockEquiv I ⟨j,hj⟩).symm ⟨c, hc⟩ with hidef
    have hbs : blockSeed I M ⟨j,hj⟩ i = M c := by
      rw [blockSeed_apply, hidef, blockColour_eq_symm hc]
    by_cases hb : f ∈ batch i
    · have hb' : f ∈ blockSeed I M ⟨j,hj⟩ i ∪ objFam (Nobj i) := hb
      rw [hbs] at hb'
      rcases hb' with hb' | hb'
      · exact Or.inl hb'
      · exact Or.inr (Or.inr hb')
    · exact Or.inr (Or.inl (hAbsNew i f hf hb))
  -- ## 11. small decompositions used by the disjointness verification
  have hNfdec : ∀ c'' ∈ Proc I j, ∀ e ∈ Nf c'', e ∈ M c'' ∨ e ∈ R
      ∨ (∃ k' ∈ procParts K j, e ∈ (P.part k').edgeSet) := by
    intro c'' hc'' e he
    by_cases hM : e ∈ M c''
    · exact Or.inl hM
    · rcases (hInvb c'' hc'').2.2 e he hM with h | ⟨k', hk', hck', hek'⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨k', hk', hek'⟩)
  have hNfA : ∀ c'' ∈ Proc I j, ∀ e ∈ Nf c'', e ∈ M c'' ∨ e ∈ R
      ∨ (∃ c₂ ∈ Proc I j, e ∈ Nf c₂) ∨ (∃ k' ∈ procParts K j, e ∈ (P.part k').edgeSet) := by
    intro c'' hc'' e he
    rcases hNfdec c'' hc'' e he with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  have hRcurM : ∀ e ∈ Rcur, ∀ c'' ∈ Proc I j, e ∉ Nf c'' := by
    intro e he c'' hc''
    rw [hRcurdef, mem_RcurOf] at he
    exact he.2 c'' hc''
  have hpartedges : ∀ k' ∈ procParts K j, (P.part k').edges ⊆ 𝓗'.edges :=
    fun k' _ => MultiHypergraph.edges_mono (P.le k')
  have hPartK : (P.part ⟨j,hj⟩).edges ⊆ 𝓗'.edges := MultiHypergraph.edges_mono (P.le ⟨j,hj⟩)
  have hpartsdisj : ∀ k' ∈ procParts K j, Disjoint (P.part k').edges (P.part ⟨j,hj⟩).edges := by
    intro k' hk'
    have hne' : k' ≠ ⟨j,hj⟩ := by
      intro h; rw [h, mem_procParts] at hk'; exact absurd hk' (by simp)
    exact EdgePartition.parts_edges_disjoint hne'
  have hNewOld : ∀ c c', c ≠ c' → c ∉ I ⟨j,hj⟩ → c' ∈ I ⟨j,hj⟩ →
      EdgeDisjointFam (Nf' c) (Nf' c') := by
    intro c c' hne hck hck'
    rw [hNfk c' hck']
    have hneProc : c' ∉ Proc I j := fun h => Proc_disjoint_block hj hIdisj c' h hck'
    have hB : ∀ f ∈ Nabs ((blockEquiv I ⟨j,hj⟩).symm ⟨c', hck'⟩),
        f ∈ M c' ∨ f ∈ Rcur ∨ f ∈ (P.part ⟨j,hj⟩).edgeSet := by
      intro f hf
      rcases hNabs_decomp c' hck' f hf with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (objFam_subset_edgeSet _ h))
    rcases em (c ∈ Proc I j) with hcj | hcnj
    · rw [hNfn c hck]
      have hAR : ∀ e ∈ Nf c, e ∈ R → ∃ c'' ∈ Proc I j, e ∈ Nf c'' := fun e he _ => ⟨c, hcj, he⟩
      exact edgeDisjointFam_old_new (A := Nf c)
        (B := Nabs ((blockEquiv I ⟨j,hj⟩).symm ⟨c', hck'⟩))
        hne hneProc hRcurSub hAR (hNfA c hcj) hNfdec hB hMdisj hMR hMout hout hRcurM
        hpartedges hPartK hpartsdisj
    · rw [hNfn c hck, hInva c hcnj]
      have hAR : ∀ e ∈ M c, e ∈ R → ∃ c'' ∈ Proc I j, e ∈ Nf c'' :=
        fun e he hR => absurd hR (hMR c e he)
      exact edgeDisjointFam_old_new (A := M c)
        (B := Nabs ((blockEquiv I ⟨j,hj⟩).symm ⟨c', hck'⟩))
        hne hneProc hRcurSub hAR (fun e he => Or.inl he) hNfdec hB hMdisj hMR hMout hout hRcurM
        hpartedges hPartK hpartsdisj
  have hOldM : ∀ c c', c ∈ Proc I j → c' ∉ I ⟨j,hj⟩ → c' ∉ Proc I j →
      EdgeDisjointFam (Nf c) (M c') := by
    intro c c' hcj hck' hcnj'
    have hne : c ≠ c' := fun h => hcnj' (h ▸ hcj)
    have hAR : ∀ e ∈ Nf c, e ∈ R → ∃ c'' ∈ Proc I j, e ∈ Nf c'' := fun e he _ => ⟨c, hcj, he⟩
    exact edgeDisjointFam_old_new (A := Nf c) (B := M c') hne hcnj' hRcurSub hAR
      (hNfA c hcj) hNfdec (fun f hf => Or.inl hf) hMdisj hMR hMout hout hRcurM
      hpartedges hPartK hpartsdisj
  refine ⟨Nf', ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (a) unprocessed colours
    intro c hc
    have hck : c ∉ I ⟨j,hj⟩ := fun h =>
      hc (by rw [Proc_succ I hj]; exact Finset.mem_union.mpr (Or.inr h))
    rw [hNfn c hck]
    exact hInva c (fun h => hc (by rw [Proc_succ I hj]; exact Finset.mem_union.mpr (Or.inl h)))
  · -- (b) processed colours
    intro c hc
    have hc' : c ∈ Proc I j ∨ c ∈ I ⟨j,hj⟩ := by
      have hh := hc
      rw [Proc_succ I hj] at hh
      exact Finset.mem_union.mp hh
    rcases hc' with hcj | hck
    · rw [hNfn c (Proc_disjoint_block hj hIdisj c hcj)]
      obtain ⟨h1, h2, h3⟩ := hInvb c hcj
      exact ⟨h1, h2, fun e he hne => by
        rcases h3 e he hne with h | ⟨k', hk', hck', hek'⟩
        · exact Or.inl h
        · exact Or.inr ⟨k', procParts_mono (Nat.le_succ j) hk', hck', hek'⟩⟩
    · rw [hNfk c hck]
      set i := (blockEquiv I ⟨j,hj⟩).symm ⟨c, hck⟩ with hidef
      have hbs : blockSeed I M ⟨j,hj⟩ i = M c := by
        rw [blockSeed_apply, hidef, blockColour_eq_symm hck]
      refine ⟨?_, ?_, ?_⟩
      · rw [← hbs]
        exact fun e he => hAbsSub i (Set.mem_union_left _ he)
      · exact hAbsMat i
      · intro e he hne
        by_cases hb : e ∈ batch i
        · refine Or.inr ⟨⟨j, hj⟩, mem_procParts.mpr (Nat.lt_succ_self j), hck, ?_⟩
          have hb' : e ∈ blockSeed I M ⟨j,hj⟩ i ∪ objFam (Nobj i) := hb
          rw [hbs] at hb'
          rcases hb' with hb' | hb'
          · exact absurd hb' hne
          · exact objFam_subset_edgeSet (Nobj i) hb'
        · exact Or.inl (hRcurSub (hAbsNew i e he hb))
  · -- (c) pairwise edge-disjointness
    intro c c' hne
    by_cases hck : c ∈ I ⟨j,hj⟩
    · by_cases hck' : c' ∈ I ⟨j,hj⟩
      · rw [hNfk c hck, hNfk c' hck']
        refine hAbsDisj _ _ ?_
        intro hcon
        exact hne (by
          have hh := congrArg (fun i => blockColour I ⟨j,hj⟩ i) hcon
          rwa [blockColour_eq_symm hck, blockColour_eq_symm hck'] at hh)
      · exact edgeDisjointFam_comm (hNewOld c' c hne.symm hck' hck)
    · by_cases hck' : c' ∈ I ⟨j,hj⟩
      · exact hNewOld c c' hne hck hck'
      · rcases em (c ∈ Proc I j) with hcj | hcnj
        · rcases em (c' ∈ Proc I j) with hcj' | hcnj'
          · rw [hNfn c hck, hNfn c' hck']
            exact hInvc c c' hne
          · rw [hNfn c hck, hNfn c' hck', hInva c' hcnj']
            exact hOldM c c' hcj hck' hcnj'
        · rcases em (c' ∈ Proc I j) with hcj' | hcnj'
          · rw [hNfn c hck, hNfn c' hck', hInva c hcnj]
            exact edgeDisjointFam_comm (hOldM c' c hcj' hck hcnj)
          · rw [hNfn c hck, hNfn c' hck', hInva c hcnj, hInva c' hcnj']
            exact hMdisj c c' hne
  · -- (d) the `R`-edges through a vertex
    intro w
    let A0 : Set (Set (Fin n)) :=
      ({e ∈ R | w ∈ e} : Set (Set (Fin n))) ∩ (⋃ c ∈ Proc I (j+1), Nf' c)
    let A1 : Set (Set (Fin n)) :=
      ({e ∈ R | w ∈ e} : Set (Set (Fin n))) ∩ (⋃ c ∈ Proc I j, Nf c)
    let A2 : Set (Set (Fin n)) :=
      ({e ∈ R | w ∈ e} : Set (Set (Fin n))) ∩ (⋃ i : Fin (I ⟨j,hj⟩).card, Nabs i)
    have hA0 : A0 = A1 ∪ A2 := by
      simp only [A0, A1, A2]
      rw [hNf'def]
      rw [iUnion_Proc_succ_extend hj hIdisj Nf Nabs, Set.inter_union_distrib_left]
    have hsplit : A0.ncard ≤ A1.ncard + A2.ncard := by
      rw [hA0]; exact Set.ncard_union_le A1 A2
    have hNEW : (A2.ncard : ℝ)
        ≤ (({i : Fin (I ⟨j,hj⟩).card | w ∉ famVert (batch i)} : Set _).ncard : ℝ) :=
      ncard_Redges_le_missing (𝓜 := 𝓗) R batch Nabs w hAbsMat hAbsSub hBatchR
    have hSub : ({i : Fin (I ⟨j,hj⟩).card | w ∉ famVert (batch i)} : Set _)
        ⊆ ({i : Fin (I ⟨j,hj⟩).card | w ∉ objVert (Nobj i)} : Set _) := by
      intro i hi
      simp only [Set.mem_setOf_eq] at hi ⊢
      intro hcon
      exact hi (famVert_mono (fun e he => Set.mem_union_right _ he) (by rwa [famVert_objFam]))
    have hMISS := ncard_miss_objVert_le Nobj w hNobjMatch hNobjLeft (hpartdeg ⟨j,hj⟩ w)
      (le_of_lt hγp0) (le_of_lt hκ0) hβp0 hpar.hβpκ hγp1 hκ1
    have hcard : ((Proc I (j+1)).card : ℝ) = ((Proc I j).card : ℝ) + ((I ⟨j,hj⟩).card : ℝ) := by
      rw [card_Proc_succ hj hIdisj]; push_cast; ring
    have h4 : (({i : Fin (I ⟨j,hj⟩).card | w ∉ famVert (batch i)} : Set _).ncard : ℝ)
        ≤ (γp + 2 * κ) * ((I ⟨j,hj⟩).card : ℝ) := by
      have h5 : (({i : Fin (I ⟨j,hj⟩).card | w ∉ famVert (batch i)} : Set _).ncard : ℝ)
          ≤ (({i : Fin (I ⟨j,hj⟩).card | w ∉ objVert (Nobj i)} : Set _).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hSub
      linarith [h5, hMISS]
    have h3 : (A1.ncard : ℝ) ≤ (γp + 2 * κ) * ((Proc I j).card : ℝ) := hInvd w
    have h6 : (A2.ncard : ℝ) ≤ (γp + 2 * κ) * ((I ⟨j,hj⟩).card : ℝ) := le_trans hNEW h4
    have h7 : (A0.ncard : ℝ) ≤ (A1.ncard : ℝ) + (A2.ncard : ℝ) := by exact_mod_cast hsplit
    have h2 : (A0.ncard : ℝ)
        ≤ ((γp + 2 * κ) * ((Proc I j).card : ℝ))
          + ((γp + 2 * κ) * ((I ⟨j,hj⟩).card : ℝ)) := by linarith [h3, h6, h7]
    change (A0.ncard : ℝ) ≤ (γp + 2 * κ) * ((Proc I (j+1)).card : ℝ)
    rw [hcard]
    linarith [h2]
  · -- (e) the leftover edges of the parts
    intro k' hk' w
    have hk'lt : k'.val < j + 1 := mem_procParts.mp hk'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk'lt with hlt | heq
    · have hk'j : k' ∈ procParts K j := mem_procParts.mpr hlt
      have hne' : k' ≠ ⟨j,hj⟩ := by
        intro h; rw [h] at hlt; exact absurd hlt (by simp)
      have hnot : ∀ c ∈ I k', c ∉ I ⟨j,hj⟩ := fun c hc =>
        (Finset.disjoint_left.mp (hIdisj k' ⟨j,hj⟩ hne')) hc
      have hun : (⋃ c ∈ I k', Nf' c) = (⋃ c ∈ I k', Nf c) := by
        ext f
        simp only [Set.mem_iUnion, exists_prop]
        constructor
        · rintro ⟨c, hc, hfc⟩
          exact ⟨c, hc, by rwa [hNfn c (hnot c hc)] at hfc⟩
        · rintro ⟨c, hc, hfc⟩
          exact ⟨c, hc, by rwa [hNfn c (hnot c hc)]⟩
      rw [hun]
      exact hInve k' hk'j w
    · have hk'eq : k' = ⟨j,hj⟩ := Fin.ext heq
      subst hk'eq
      have hidx : ∀ i : Fin (I ⟨j,hj⟩).card,
          (blockEquiv I ⟨j,hj⟩).symm ⟨blockColour I ⟨j,hj⟩ i, blockColour_mem I ⟨j,hj⟩ i⟩ = i := by
        intro i
        have h1 : (⟨blockColour I ⟨j,hj⟩ i, blockColour_mem I ⟨j,hj⟩ i⟩ : ↥(I ⟨j,hj⟩))
            = blockEquiv I ⟨j,hj⟩ i := Subtype.ext rfl
        rw [h1, Equiv.symm_apply_apply]
      have hUnionCov : (⋃ c ∈ I ⟨j,hj⟩, Nf' c) = (⋃ i : Fin (I ⟨j,hj⟩).card, Nabs i) := by
        ext f
        simp only [Set.mem_iUnion, exists_prop]
        constructor
        · rintro ⟨c, hc, hfc⟩
          exact ⟨(blockEquiv I ⟨j,hj⟩).symm ⟨c, hc⟩, by rwa [hNfk c hc] at hfc⟩
        · rintro ⟨i, hfi⟩
          exact ⟨blockColour I ⟨j,hj⟩ i, blockColour_mem I ⟨j,hj⟩ i, by
            rw [show Nf' (blockColour I ⟨j,hj⟩ i) = Nabs i from by
              rw [hNf'def]; exact extend_blockColour Nabs i]
            exact hfi⟩
      rw [hUnionCov]
      have hUnionInt : (⋃ i : Fin (I ⟨j,hj⟩).card, Nabs i) ∩ (P.part ⟨j,hj⟩).edgeSet
          = (⋃ i : Fin (I ⟨j,hj⟩).card, objFam (Nobj i)) ∩ (P.part ⟨j,hj⟩).edgeSet := by
        ext f
        constructor
        · rintro ⟨hf, hfS⟩
          obtain ⟨i, hfi⟩ := Set.mem_iUnion.mp hf
          have hfi' : f ∈ Nabs ((blockEquiv I ⟨j,hj⟩).symm
              ⟨blockColour I ⟨j,hj⟩ i, blockColour_mem I ⟨j,hj⟩ i⟩) := by rwa [hidx i]
          rcases hNabs_decomp (blockColour I ⟨j,hj⟩ i) (blockColour_mem I ⟨j,hj⟩ i) f hfi'
            with h | h | h
          · exact absurd (MultiHypergraph.edgeSet_mono (P.le ⟨j,hj⟩) hfS) (hMout _ f h)
          · exact absurd (hRcurSub h) (edgeSet_not_mem_of_out hout hR2 f
              (MultiHypergraph.edgeSet_mono (P.le ⟨j,hj⟩) hfS))
          · rw [hidx i] at h
            exact ⟨Set.mem_iUnion.mpr ⟨i, h⟩, hfS⟩
        · rintro ⟨hf, hfS⟩
          obtain ⟨i, hfi⟩ := Set.mem_iUnion.mp hf
          refine ⟨?_, hfS⟩
          exact Set.mem_iUnion.mpr ⟨i, hAbsSub i (Set.mem_union_right _ hfi)⟩
      have hseteq : ({e ∈ (P.part ⟨j,hj⟩).edgeSet | w ∈ e} \ (⋃ i, Nabs i))
          = ({e ∈ (P.part ⟨j,hj⟩).edgeSet | w ∈ e} \ (⋃ i, objFam (Nobj i))) := by
        ext f
        constructor
        · rintro ⟨hfS, hfA⟩
          refine ⟨hfS, fun hfB => hfA ?_⟩
          have hh : f ∈ (⋃ i, Nabs i) ∩ (P.part ⟨j,hj⟩).edgeSet := by
            rw [hUnionInt]; exact ⟨hfB, hfS.1⟩
          exact hh.1
        · rintro ⟨hfS, hfB⟩
          refine ⟨hfS, fun hfA => hfB ?_⟩
          have hh : f ∈ (⋃ i, objFam (Nobj i)) ∩ (P.part ⟨j,hj⟩).edgeSet := by
            rw [← hUnionInt]; exact ⟨hfA, hfS.1⟩
          exact hh.1
      have huncov := ncard_uncovered_le_unused (𝓜 := P.part ⟨j,hj⟩)
        (MultiHypergraph.isLinear_mono (P.le ⟨j,hj⟩) hlin') Nobj w
      have hleftw := leftover_bound (𝓜 := P.part ⟨j,hj⟩) Nobj w hNobjLeft
        (hpartdeg ⟨j,hj⟩ w) (le_of_lt hγp0) (le_of_lt hκ0) hβp0 hpar.hβpκ hγp1 hκ1
      calc ((({e ∈ (P.part ⟨j,hj⟩).edgeSet | w ∈ e} \ (⋃ i, Nabs i)).ncard : ℝ))
          = (({e ∈ (P.part ⟨j,hj⟩).edgeSet | w ∈ e} \ (⋃ i, objFam (Nobj i))).ncard : ℝ) := by
            rw [hseteq]
        _ ≤ (({x ∈ objThrough (P.part ⟨j,hj⟩) w | ∀ i, x ∉ Nobj i} : Set _).ncard : ℝ) := by
            exact_mod_cast huncov
        _ ≤ (γp + 2 * κ) * ((I ⟨j,hj⟩).card : ℝ) := hleftw
  · -- (f) the coverage of `U`
    refine ⟨?_, ?_⟩
    · intro hbig
      have hmissSet : ∀ u ∈ U,
          (({c ∈ Proc I j | u ∉ famVert (Nf c)} : Set (Fin D)).ncard) ≤ 1 := by
        intro u hu
        have h1 := (hInvf.1 hbig).1 u hu
        have h2 : ((((Proc I j).filter (fun c => u ∈ famVert (Nf c))).card : ℕ) : ℝ) + 1
            ≥ ((Proc I j).card : ℝ) := by
          have hh := ncard_setOf_mem_finset (Proc I j) (fun c => u ∈ famVert (Nf c))
          rw [hh] at h1
          exact h1
        have h3 := Finset.card_filter_add_card_filter_not (s := Proc I j)
          (fun c => u ∈ famVert (Nf c))
        have h2n : (Proc I j).card ≤ ((Proc I j).filter (fun c => u ∈ famVert (Nf c))).card + 1 := by
          have h2' : (((Proc I j).card : ℕ) : ℝ)
              ≤ ((((Proc I j).filter (fun c => u ∈ famVert (Nf c))).card : ℕ) : ℝ) + 1 := by
            push_cast
            linarith [h2]
          exact_mod_cast h2'
        have h4 : ((Proc I j).filter (fun c => u ∉ famVert (Nf c))).card ≤ 1 := by omega
        rw [ncard_setOf_mem_finset (Proc I j) (fun c => u ∉ famVert (Nf c))]
        exact h4
      have hnewSet : ∀ u ∈ U,
          (({i : Fin (I ⟨j,hj⟩).card | u ∉ famVert (Nabs i)} : Set _).ncard) ≤ 1 := by
        intro u hu
        have h1 := (hAbsNear hbig).1 u hu
        have h1' : (({i : Fin (I ⟨j,hj⟩).card | u ∈ famVert (Nabs i)} : Set _).ncard : ℝ)
            = ((((Finset.univ : Finset (Fin (I ⟨j,hj⟩).card)).filter
                (fun i => u ∈ famVert (Nabs i))).card : ℕ) : ℝ) := by
          have hE : ({i : Fin (I ⟨j,hj⟩).card | u ∈ famVert (Nabs i)} : Set _)
              = (((Finset.univ : Finset (Fin (I ⟨j,hj⟩).card)).filter
                  (fun i => u ∈ famVert (Nabs i))) : Set _) := by
            ext i
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
              Set.mem_setOf_eq]
          rw [hE, Set.ncard_coe_finset]
        rw [h1'] at h1
        have h3 := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin (I ⟨j,hj⟩).card)))
          (fun i => u ∈ famVert (Nabs i))
        have h3n : (Finset.univ : Finset (Fin (I ⟨j,hj⟩).card)).card
            ≤ ((Finset.univ : Finset (Fin (I ⟨j,hj⟩).card)).filter
                (fun i => u ∈ famVert (Nabs i))).card + 1 := by
          have h2' : ((((Finset.univ : Finset (Fin (I ⟨j,hj⟩).card)).filter
                  (fun i => u ∈ famVert (Nabs i))).card : ℕ) : ℝ) + 1
              ≥ ((I ⟨j,hj⟩).card : ℝ) := by
            have hh := h1
            rw [Fintype.card_fin] at hh
            linarith [hh]
          have h2'' : ((I ⟨j,hj⟩).card : ℕ)
              ≤ ((Finset.univ : Finset (Fin (I ⟨j,hj⟩).card)).filter
                  (fun i => u ∈ famVert (Nabs i))).card + 1 := by exact_mod_cast h2'
          rwa [Finset.card_univ, Fintype.card_fin]
        have h4 : ((Finset.univ : Finset (Fin (I ⟨j,hj⟩).card)).filter
            (fun i => u ∉ famVert (Nabs i))).card ≤ 1 := by omega
        have hE : ({i : Fin (I ⟨j,hj⟩).card | u ∉ famVert (Nabs i)} : Set _)
            = (((Finset.univ : Finset (Fin (I ⟨j,hj⟩).card)).filter
                (fun i => u ∉ famVert (Nabs i))) : Set _) := by
          ext i
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
            Set.mem_setOf_eq]
        rw [hE, Set.ncard_coe_finset]
        exact h4
      have hmix : ∀ u ∈ U, ∀ (c : Fin D), c ∈ Proc I j → u ∉ famVert (Nf c) →
          ∀ i, u ∉ famVert (Nabs i) → False := by
        intro u hu c hcj hcu i hiu
        have h1 : U \ famVert (Nf c) = {u} := by
          have h2 : (U \ famVert (Nf c)).ncard ≤ 1 := (hInvf.1 hbig).2.2 c hcj
          have hu1 : u ∈ U \ famVert (Nf c) := ⟨hu, hcu⟩
          rw [Set.ncard_le_one] at h2
          exact Set.eq_singleton_iff_unique_mem.mpr ⟨hu1, fun y hy => h2 y hy u hu1⟩
        have h2 : u ∉ Scur := by
          intro hcon
          rw [hScurdef, mem_ScurOf] at hcon
          exact hcon.2 c hcj (by rw [h1, Set.mem_singleton_iff])
        have h3 : u ∈ Scur := (hAbsNear hbig).2.1 i ⟨hu, hiu⟩
        exact h2 h3
      refine ⟨?_, ?_, ?_⟩
      · intro u hu
        have hold := hmissSet u hu
        have hnew := hnewSet u hu
        have hmiss : (((Proc I (j+1)).filter (fun c => u ∉ famVert (Nf' c))).card) ≤ 1 := by
          rw [Finset.card_le_one]
          intro a ha b hb
          rw [Finset.mem_filter] at ha hb
          have hac : a ∈ Proc I j ∨ a ∈ I ⟨j,hj⟩ := by
            have hh := ha.1; rw [Proc_succ I hj] at hh; exact Finset.mem_union.mp hh
          have hbc : b ∈ Proc I j ∨ b ∈ I ⟨j,hj⟩ := by
            have hh := hb.1; rw [Proc_succ I hj] at hh; exact Finset.mem_union.mp hh
          rcases hac with haj | hak <;> rcases hbc with hbj | hbk
          · have ha2 : u ∉ famVert (Nf a) := by
              have hh := ha.2
              rwa [hNfn a (Proc_disjoint_block hj hIdisj a haj)] at hh
            have hb2 : u ∉ famVert (Nf b) := by
              have hh := hb.2
              rwa [hNfn b (Proc_disjoint_block hj hIdisj b hbj)] at hh
            exact (Set.ncard_le_one (s := {c ∈ Proc I j | u ∉ famVert (Nf c)})).mp hold
              a ⟨haj, ha2⟩ b ⟨hbj, hb2⟩
          · have ha2 : u ∉ famVert (Nf a) := by
              have hh := ha.2
              rwa [hNfn a (Proc_disjoint_block hj hIdisj a haj)] at hh
            have hbi : u ∉ famVert (Nabs ((blockEquiv I ⟨j,hj⟩).symm ⟨b, hbk⟩)) := by
              have hh := hb.2
              rwa [hNfk b hbk] at hh
            exact (hmix u hu a haj ha2 _ hbi).elim
          · have hai : u ∉ famVert (Nabs ((blockEquiv I ⟨j,hj⟩).symm ⟨a, hak⟩)) := by
              have hh := ha.2
              rwa [hNfk a hak] at hh
            have hb2 : u ∉ famVert (Nf b) := by
              have hh := hb.2
              rwa [hNfn b (Proc_disjoint_block hj hIdisj b hbj)] at hh
            exact (hmix u hu b hbj hb2 _ hai).elim
          · have hai : u ∉ famVert (Nabs ((blockEquiv I ⟨j,hj⟩).symm ⟨a, hak⟩)) := by
              have hh := ha.2
              rwa [hNfk a hak] at hh
            have hbi : u ∉ famVert (Nabs ((blockEquiv I ⟨j,hj⟩).symm ⟨b, hbk⟩)) := by
              have hh := hb.2
              rwa [hNfk b hbk] at hh
            have h1 : (blockEquiv I ⟨j,hj⟩).symm ⟨a, hak⟩
                = (blockEquiv I ⟨j,hj⟩).symm ⟨b, hbk⟩ :=
              (Set.ncard_le_one (s := {i : Fin (I ⟨j,hj⟩).card | u ∉ famVert (Nabs i)})).mp hnew
                _ hai _ hbi
            have h2 := congrArg (fun i => blockColour I ⟨j,hj⟩ i) h1
            rwa [blockColour_eq_symm hak, blockColour_eq_symm hbk] at h2
        have hcard := Finset.card_filter_add_card_filter_not (s := Proc I (j+1))
          (fun c => u ∈ famVert (Nf' c))
        have h6 : ((((Proc I (j+1)).filter (fun c => u ∉ famVert (Nf' c))).card : ℕ) : ℝ) ≤ 1 := by
          exact_mod_cast hmiss
        have h7 : (({c ∈ Proc I (j+1) | u ∈ famVert (Nf' c)} : Set (Fin D)).ncard : ℝ)
            = ((((Proc I (j+1)).filter (fun c => u ∈ famVert (Nf' c))).card : ℕ) : ℝ) := by
          rw [ncard_setOf_mem_finset]
        rw [h7]
        have h8 := congrArg (Nat.cast : ℕ → ℝ) hcard
        push_cast at h8
        linarith
      · intro c hc
        have hc' : c ∈ Proc I j ∨ c ∈ I ⟨j,hj⟩ := by
          have hh := hc; rw [Proc_succ I hj] at hh; exact Finset.mem_union.mp hh
        rcases hc' with hcj | hck
        · rw [hNfn c (Proc_disjoint_block hj hIdisj c hcj)]
          exact (hInvf.1 hbig).2.1 c hcj
        · rw [hNfk c hck]
          exact fun x hx => hScurSub ((hAbsNear hbig).2.1 _ hx)
      · intro c hc
        have hc' : c ∈ Proc I j ∨ c ∈ I ⟨j,hj⟩ := by
          have hh := hc; rw [Proc_succ I hj] at hh; exact Finset.mem_union.mp hh
        rcases hc' with hcj | hck
        · rw [hNfn c (Proc_disjoint_block hj hIdisj c hcj)]
          exact (hInvf.1 hbig).2.2 c hcj
        · rw [hNfk c hck]
          exact (hAbsNear hbig).2.2 _
    · intro hsmall c hc
      have hc' : c ∈ Proc I j ∨ c ∈ I ⟨j,hj⟩ := by
        have hh := hc; rw [Proc_succ I hj] at hh; exact Finset.mem_union.mp hh
      rcases hc' with hcj | hck
      · rw [hNfn c (Proc_disjoint_block hj hIdisj c hcj)]
        exact hInvf.2 hsmall c hcj
      · rw [hNfk c hck]
        exact hAbsCov (not_lt.mp hsmall) _
  · -- (g) the singleton bookkeeping
    intro w
    have hOld : ((Proc I j).filter (fun c => ({w} : Set (Fin n)) ∈ Nf' c ∧
        ({w} : Set (Fin n)) ∉ M c)).card
        = ((Proc I j).filter (fun c => ({w} : Set (Fin n)) ∈ Nf c ∧
            ({w} : Set (Fin n)) ∉ M c)).card := by
      congr 1
      apply Finset.filter_congr
      intro c hc
      rw [hNfn c (Proc_disjoint_block hj hIdisj c hc)]
    have hNew : ((I ⟨j,hj⟩).filter (fun c => ({w} : Set (Fin n)) ∈ Nf' c ∧
        ({w} : Set (Fin n)) ∉ M c)).card ≤ (P.part ⟨j,hj⟩).singles w := by
      have hidx : ∀ i : Fin (I ⟨j,hj⟩).card,
          (blockEquiv I ⟨j,hj⟩).symm ⟨blockColour I ⟨j,hj⟩ i, blockColour_mem I ⟨j,hj⟩ i⟩ = i := by
        intro i
        have h1 : (⟨blockColour I ⟨j,hj⟩ i, blockColour_mem I ⟨j,hj⟩ i⟩ : ↥(I ⟨j,hj⟩))
            = blockEquiv I ⟨j,hj⟩ i := Subtype.ext rfl
        rw [h1, Equiv.symm_apply_apply]
      let Q : Fin (I ⟨j,hj⟩).card → Prop := fun i =>
        ({w} : Set (Fin n)) ∈ Nf' (blockColour I ⟨j,hj⟩ i) ∧
          ({w} : Set (Fin n)) ∉ M (blockColour I ⟨j,hj⟩ i)
      have hbij : ((I ⟨j,hj⟩).filter (fun c => ({w} : Set (Fin n)) ∈ Nf' c ∧
          ({w} : Set (Fin n)) ∉ M c)).card
          = ((Finset.univ : Finset (Fin (I ⟨j,hj⟩).card)).filter Q).card := by
        rw [← Finset.card_image_of_injective
          (f := blockColour I ⟨j,hj⟩)
          ((Finset.univ : Finset (Fin (I ⟨j,hj⟩).card)).filter Q)
          (blockColour_injective I ⟨j,hj⟩)]
        congr 1
        ext c
        constructor
        · intro hc
          obtain ⟨hc1, hc2⟩ := Finset.mem_filter.mp hc
          obtain ⟨i, hi⟩ := exists_blockColour hc1
          refine Finset.mem_image.mpr ⟨i, ?_, hi⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          change ({w} : Set (Fin n)) ∈ Nf' (blockColour I ⟨j,hj⟩ i) ∧
            ({w} : Set (Fin n)) ∉ M (blockColour I ⟨j,hj⟩ i)
          rw [hi]; exact hc2
        · intro hc
          obtain ⟨i, hi, hci⟩ := Finset.mem_image.mp hc
          obtain ⟨-, hQ⟩ := Finset.mem_filter.mp hi
          change ({w} : Set (Fin n)) ∈ Nf' (blockColour I ⟨j,hj⟩ i) ∧
            ({w} : Set (Fin n)) ∉ M (blockColour I ⟨j,hj⟩ i) at hQ
          exact Finset.mem_filter.mpr ⟨by rw [← hci]; exact blockColour_mem I ⟨j,hj⟩ i,
            by rw [hci] at hQ; exact hQ⟩
      rw [hbij]
      have hsub : (((Finset.univ : Finset (Fin (I ⟨j,hj⟩).card)).filter Q).card)
          ≤ (({i : Fin (I ⟨j,hj⟩).card | ({w} : Set (Fin n)) ∈ objFam (Nobj i)} :
              Set _).ncard) := by
        have h1 : (((Finset.univ : Finset (Fin (I ⟨j,hj⟩).card)).filter Q).card)
            ≤ (((Finset.univ : Finset (Fin (I ⟨j,hj⟩).card)).filter
                (fun i => ({w} : Set (Fin n)) ∈ objFam (Nobj i))).card) := by
          apply Finset.card_le_card
          intro i hi
          obtain ⟨-, hiQ⟩ := Finset.mem_filter.mp hi
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have hNfi : ({w} : Set (Fin n)) ∈ Nabs i := by
            have hh := hiQ.1
            rwa [show Nf' (blockColour I ⟨j,hj⟩ i) = Nabs i from by
              rw [hNf'def]; exact extend_blockColour Nabs i] at hh
          have hfi' : ({w} : Set (Fin n)) ∈ Nabs ((blockEquiv I ⟨j,hj⟩).symm
              ⟨blockColour I ⟨j,hj⟩ i, blockColour_mem I ⟨j,hj⟩ i⟩) := by rwa [hidx i]
          rcases hNabs_decomp (blockColour I ⟨j,hj⟩ i) (blockColour_mem I ⟨j,hj⟩ i) {w} hfi'
            with h | h | h
          · exact absurd h hiQ.2
          · exfalso
            have h2 : edgeSize ({w} : Set (Fin n)) = 2 := hR2 _ (hRcurSub h)
            rw [edgeSize_eq_ncard, Set.ncard_singleton] at h2
            exact absurd h2 (by norm_num)
          · rw [hidx i] at h
            exact h
        have hE : (((Finset.univ : Finset (Fin (I ⟨j,hj⟩).card)).filter
            (fun i => ({w} : Set (Fin n)) ∈ objFam (Nobj i))).card)
            = (({i : Fin (I ⟨j,hj⟩).card | ({w} : Set (Fin n)) ∈ objFam (Nobj i)} :
                Set _).ncard) := by
          have hE2 : ({i : Fin (I ⟨j,hj⟩).card | ({w} : Set (Fin n)) ∈ objFam (Nobj i)} : Set _)
              = (((Finset.univ : Finset (Fin (I ⟨j,hj⟩).card)).filter
                  (fun i => ({w} : Set (Fin n)) ∈ objFam (Nobj i))) : Set _) := by
            ext i
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
              Set.mem_setOf_eq]
          rw [hE2, Set.ncard_coe_finset]
        exact le_trans h1 (le_of_eq hE)
      have hcnt := ncard_colours_singleton_le (𝓜 := P.part ⟨j,hj⟩)
        (MultiHypergraph.isLinear_mono (P.le ⟨j,hj⟩) hlin') Nobj hNobjMatch hNobjDisj w
      exact le_trans hsub hcnt
    have hsplit : ((Proc I (j+1)).filter (fun c => ({w} : Set (Fin n)) ∈ Nf' c ∧
        ({w} : Set (Fin n)) ∉ M c)).card
        = ((Proc I j).filter (fun c => ({w} : Set (Fin n)) ∈ Nf' c ∧
            ({w} : Set (Fin n)) ∉ M c)).card
          + ((I ⟨j,hj⟩).filter (fun c => ({w} : Set (Fin n)) ∈ Nf' c ∧
              ({w} : Set (Fin n)) ∉ M c)).card := by
      rw [Proc_succ I hj, Finset.filter_union]
      refine Finset.card_union_of_disjoint ?_
      rw [Finset.disjoint_iff_ne]
      intro a ha b hb hab
      subst hab
      exact Proc_disjoint_block hj hIdisj a (Finset.mem_filter.mp ha).1
        (Finset.mem_filter.mp hb).1
    rw [hsplit]
    have h1 : ((((Proc I j).filter (fun c => ({w} : Set (Fin n)) ∈ Nf' c ∧
        ({w} : Set (Fin n)) ∉ M c)).card : ℕ) : ℝ) ≤ asmSinglesSum 𝓗' P j w := by
      have hh := hInvg w
      rwa [hOld]
    have h2 : ((((I ⟨j,hj⟩).filter (fun c => ({w} : Set (Fin n)) ∈ Nf' c ∧
        ({w} : Set (Fin n)) ∉ M c)).card : ℕ) : ℝ) ≤ ((P.part ⟨j,hj⟩).singles w : ℝ) := by
      exact_mod_cast hNew
    have h3 : asmSinglesSum 𝓗' P (j+1) w
        = asmSinglesSum 𝓗' P j w + ((P.part ⟨j,hj⟩).singles w : ℝ) := asmSinglesSum_succ P hj w
    rw [h3]
    push_cast
    linarith

end Work.Deep.Nibble
