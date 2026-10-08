import Mathlib
import Submission.Work.BSW.BSW36.exists_normal_complement_le

namespace Work.BSW.BSW36

/-- **Normal Sylow from self-centralizing normalizers of all other Sylow subgroups.**

Let `N` be a finite group and `p` a prime.  Suppose that for every prime `r ≠ p` and every Sylow
`r`-subgroup `R` of `N` the normalizer of `R` is contained in its centralizer,
`N_N(R) ≤ C_N(R)` (equivalently `R ≤ Z(N_N(R))`).  Then the Sylow `p`-subgroups of `N` are
normal, i.e. there is a unique one.

Proof.  For each prime `q ≠ p` the hypothesis is exactly the hypothesis of *Burnside's normal
`q`-complement theorem* (Mathlib's `MonoidHom.ker_transferSylow_isComplement'`), so `N` possesses
a normal `q`-complement `M_q ⊴ N` with `G ⧸ M_q` a `q`-group; in particular `q ∤ |M_q|` and every
Sylow `p`-subgroup (a `p`-group with `p ≠ q`) is contained in `M_q`.  Let `K = ⋂_{q ≠ p} M_q`
(intersection over the primes `q ≠ p` dividing `|N|`).  It is normal; dividing `|K|` each `|M_q|`
shows `|K|` is a power of `p`, so `K` is a `p`-group, and it contains every Sylow `p`-subgroup;
hence `K` *is* the unique Sylow `p`-subgroup of `N`. -/
theorem normal_sylow_of_forall_sylow_normalizer_le_centralizer
    {N : Type} [Group N] [Finite N] {p : ℕ} (hp : p.Prime)
    (h : ∀ (r : ℕ) (hr : r.Prime), r ≠ p → ∀ (R : Sylow r N),
        (Subgroup.normalizer ((R : Subgroup N) : Set N) : Subgroup N) ≤
          Subgroup.centralizer ((R : Subgroup N) : Set N)) :
    ∃ L : Subgroup N, L.Normal ∧ IsPGroup p L ∧
      (∀ P : Sylow p N, (P : Subgroup N) = L) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  -- `S` is the set of primes `≠ p` dividing `|N|`.
  set S : Finset ℕ := (Nat.card N).primeFactors.erase p with hS
  -- For each `q ∈ S` there is a normal `q`-complement containing every Sylow `p`-subgroup.
  have hkey : ∀ q ∈ S, ∃ M : Subgroup N, M.Normal ∧ ¬ q ∣ Nat.card M ∧
      (∀ P : Sylow p N, (P : Subgroup N) ≤ M) := by
    intro q hq
    rw [hS, Finset.mem_erase, Nat.mem_primeFactors] at hq
    exact exists_normal_complement_le h hq.2.1 hq.1
  let Mf : {q // q ∈ S} → Subgroup N := fun q => Classical.choose (hkey q.1 q.2)
  let K : Subgroup N := ⨅ q : {q // q ∈ S}, Mf q
  have hMnorm : ∀ q : {q // q ∈ S}, (Mf q).Normal :=
    fun q => (Classical.choose_spec (hkey q.1 q.2)).1
  have hMndvd : ∀ q : {q // q ∈ S}, ¬ q.1 ∣ Nat.card (Mf q) :=
    fun q => (Classical.choose_spec (hkey q.1 q.2)).2.1
  have hMle : ∀ q : {q // q ∈ S}, ∀ P : Sylow p N, (P : Subgroup N) ≤ Mf q :=
    fun q => (Classical.choose_spec (hkey q.1 q.2)).2.2
  have hKnormal : K.Normal := Subgroup.normal_iInf_normal hMnorm
  have hPK : ∀ P : Sylow p N, (P : Subgroup N) ≤ K := fun P => le_iInf fun q => hMle q P
  have hKdvd : Nat.card K ∣ Nat.card N := by
    have h := Subgroup.card_dvd_of_le (H := K) (K := (⊤ : Subgroup N)) le_top
    simpa using h
  -- `|K|` is a power of `p`: no prime `q ≠ p` divides it.
  have hKp : IsPGroup p K := by
    rw [isPGroup_iff_primeFactors_card_subset hp.ne_zero]
    intro r hr
    rw [Nat.mem_primeFactors] at hr ⊢
    obtain ⟨hrp, hrK, -⟩ := hr
    have hrN : r ∣ Nat.card N := hrK.trans hKdvd
    have hne : Nat.card N ≠ 0 := Nat.card_pos.ne'
    by_cases hrpe : r = p
    · rw [hrpe]
      exact ⟨hp, dvd_rfl, hp.ne_zero⟩
    · exfalso
      have hrS : r ∈ S := by
        rw [hS, Finset.mem_erase, Nat.mem_primeFactors]
        exact ⟨hrpe, hrp, hrN, hne⟩
      exact (hMndvd ⟨r, hrS⟩)
        (hrK.trans (Subgroup.card_dvd_of_le (iInf_le Mf ⟨r, hrS⟩)))
  refine ⟨K, hKnormal, hKp, ?_⟩
  -- Every Sylow `p`-subgroup equals `K`, which contains it and is a `p`-group of the same order.
  intro P
  obtain ⟨P', hKP'⟩ := hKp.exists_le_sylow
  have hdvd : Nat.card K ∣ Nat.card (P : Subgroup N) := by
    have h := Subgroup.card_dvd_of_le hKP'
    rw [Sylow.card_eq_multiplicity P'] at h
    rwa [Sylow.card_eq_multiplicity P]
  exact Subgroup.eq_of_le_of_card_ge (hPK P) (Nat.le_of_dvd Nat.card_pos hdvd)

end Work.BSW.BSW36
