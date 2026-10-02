import Submission.Work.Deep.Nibble.ObjDefs
import Submission.Work.Deep.Nibble.FamDefs
import Submission.Work.Deep.Nibble.objThrough_ncard
import Submission.Work.Deep.Nibble.Glue
import Submission.Work.Deep.Nibble.Blocks
import Submission.Work.Deep.Nibble.AbsorbImport
import Submission.Work.Deep.Nibble.exists_edgePartition
import Submission.Work.Deep.Nibble.MultiAbsorb
import Submission.Work.Deep.Nibble.objCover

set_option autoImplicit false
open scoped BigOperators

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

/-- The cone's `Hypergraph` shadows Mathlib's root-level `Hypergraph` in this
file: the statement of the §7 assembly is written in the cone's vocabulary. -/
local notation "Hypergraph" => ErdosFaberLovaszConjecture.Hypergraph

noncomputable section

/-- The slack constant used by the §7 assembly: the pseudorandomness error
`κ(1+βp) + 1/n` absorbs the vertex sets of the seeds `M c` (of size
`≤ βD ≤ βp κ n`) while still satisfying the absorption margins. -/
def slackκ (κ βp : ℝ) (n : ℕ) : ℝ := κ * (1 + βp) + 1 / (n : ℝ)

theorem slackκ_le {κ βp : ℝ} {n : ℕ} (hκ : 0 ≤ κ) (hβp : βp ≤ 1 / 10)
    (h1n : 1 / (n : ℝ) ≤ κ / 2) : slackκ κ βp n ≤ (8 / 5) * κ := by
  have h1 : κ * (1 + βp) ≤ κ * (1 + 1 / 10 : ℝ) := by nlinarith
  simp only [slackκ]
  linarith

/-- **The absorption margins at the slack constant.** -/
theorem internalMargins_slack {n : ℕ} {ρ ε γ κ ξ βp : ℝ}
    (hn : 2 ≤ κ * (n : ℝ)) (hβp0 : 0 ≤ βp) (hβp1 : βp ≤ 1 / 10)
    (hm : InternalMargins n ρ ε γ κ ξ) (hκγ2' : 200 * κ ≤ γ ^ 2) :
    InternalMargins n ρ ε γ (slackκ κ βp n) ξ := by
  have hnne : n ≠ 0 := by
    rintro rfl
    simp only [Nat.cast_zero, mul_zero] at hn
    linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hnne
  have h1n : 1 / (n : ℝ) ≤ κ / 2 := by
    rw [div_le_div_iff₀ hnpos (by norm_num : (0:ℝ) < 2)]
    linarith
  have hκnn : (0:ℝ) ≤ κ := le_of_lt hm.hκ
  have hsk := slackκ_le hκnn hβp1 h1n
  have h4000 : 4000 * κ ≤ γ := by
    have h := hm.hκγρ
    have hρ0 : (0:ℝ) ≤ ρ := le_of_lt hm.hρ
    nlinarith [hm.hρ1, hm.hγ]
  have h32000 : 32000 * κ ≤ γ * ρ := by
    have h1 : (8 : ℝ) * κ ≤ γ * ρ * ε := hm.hκγε
    have h3 : 8 * κ / ε ≤ γ * ρ := (div_le_iff₀ hm.hε).mpr (by linarith)
    have h4 : 32000 * κ ≤ 8 * κ / ε := by
      rw [le_div_iff₀ hm.hε]
      nlinarith [hm.hκ, hm.hε4]
    linarith
  have hρε : 4000 * κ ≤ γ * ρ * ε := by
    have h1 : 40 * γ ≤ ρ * ε := hm.hγε
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hm.hγ)
    have h3 : 100 * κ ≤ γ ^ 2 := hm.hκγ2
    nlinarith
  have hka0 : 0 < slackκ κ βp n := by
    have h1 : (0:ℝ) < κ * (1 + βp) := mul_pos hm.hκ (by linarith)
    have h2 : (0:ℝ) < 1 / (n : ℝ) := one_div_pos.mpr hnpos
    simp only [slackκ]; linarith
  refine ⟨hm.hρ, hm.hρ1, hm.hε, hm.hγ, hka0, hm.hξ, hm.hε4, hm.hγρ, ?_, ?_, hm.hnbig,
    hm.hξγρ, hm.hγε, ?_, ?_, hm.hεhalf, hm.hγhalf, hm.hγn⟩
  · show 1500 * slackκ κ βp n ≤ γ
    nlinarith [hsk, h4000]
  · show 4000 * slackκ κ βp n ≤ γ * ρ
    nlinarith [hsk, h32000]
  · show 8 * slackκ κ βp n ≤ γ * ρ * ε
    nlinarith [hsk, hρε]
  · show 100 * slackκ κ βp n ≤ γ ^ 2
    nlinarith [hsk, hκγ2']

/-- **The crossing margins at the slack constant.** -/
theorem crossingMargins_slack {n : ℕ} {ρ ε γ κ ξ βp : ℝ}
    (hn : 2 ≤ κ * (n : ℝ)) (hβp0 : 0 ≤ βp) (hβp1 : βp ≤ 1 / 10)
    (hm : InternalMargins n ρ ε γ κ ξ) (hc : CrossingMargins n ρ ε γ κ ξ) :
    CrossingMargins n ρ ε γ (slackκ κ βp n) ξ := by
  have hnne : n ≠ 0 := by
    rintro rfl
    simp only [Nat.cast_zero, mul_zero] at hn
    linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hnne
  have h1n : 1 / (n : ℝ) ≤ κ / 2 := by
    rw [div_le_div_iff₀ hnpos (by norm_num : (0:ℝ) < 2)]
    linarith
  have hκnn : (0:ℝ) ≤ κ := le_of_lt hm.hκ
  have hsk := slackκ_le hκnn hβp1 h1n
  have h4000 : 4000 * κ ≤ γ * ρ := hm.hκγρ
  have hka0 : 0 < slackκ κ βp n := by
    have h1 : (0:ℝ) < κ * (1 + βp) := mul_pos hm.hκ (by linarith)
    have h2 : (0:ℝ) < 1 / (n : ℝ) := one_div_pos.mpr hnpos
    simp only [slackκ]; linarith
  refine ⟨hc.hn, hc.hρ, hc.hε, hc.hγ, hka0, hc.hξ, hc.hε2, hc.hρ2, ?_, hc.hγρ,
    hc.hξρ, hc.hξγρ⟩
  show 1000 * slackκ κ βp n ≤ γ * ρ
  nlinarith [hsk, h4000]


/-! ## Vertex sets of object families -/

theorem famVert_objFam {n : ℕ} {𝓜 : MultiHypergraph n} (N : Set (EdgeObj 𝓜)) :
    famVert (objFam N) = objVert N := by
  ext v
  rw [mem_famVert]
  constructor
  · rintro ⟨e, ⟨x, hx, rfl⟩, hve⟩
    exact mem_objVert.mpr ⟨x, hx, hve⟩
  · intro hv
    obtain ⟨x, hx, hvx⟩ := mem_objVert.mp hv
    exact ⟨EdgeObj.toSet x, ⟨x, hx, rfl⟩, hvx⟩

/-! ## The family of sets handed to `lem:pseudorandom_matching` -/

/-- The family `𝓕(R) ∪ {U, S, ∅}` of vertex sets with respect to which the
§7 assembly asks for pseudorandomness. -/
def absorbFam {n : ℕ} (R : Hypergraph (Fin n)) (U S : Set (Fin n)) : Set (Set (Fin n)) :=
  absorberFam R U ∪ {U, S, ∅}

theorem absorbFam_subset_internal {n : ℕ} (R : Hypergraph (Fin n)) (U S : Set (Fin n)) :
    absorberFam R U ∪ {U, S} ⊆ absorbFam R U S := by
  intro X hX
  rcases hX with h | h
  · exact Or.inl h
  · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rw [absorbFam, Set.mem_union]
    rcases h with rfl | rfl
    · exact Or.inr (by simp)
    · exact Or.inr (by simp)

theorem absorbFam_subset_crossing {n : ℕ} (R : Hypergraph (Fin n)) (U S : Set (Fin n)) :
    absorberFam R U ∪ {U, ∅} ⊆ absorbFam R U S := by
  intro X hX
  rcases hX with h | h
  · exact Or.inl h
  · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rw [absorbFam, Set.mem_union]
    rcases h with rfl | rfl
    · exact Or.inr (by simp)
    · exact Or.inr (by simp)

/-- The family of *shifted* sets `X ∖ V(M c)` handed to `lem:pseudorandom_matching`
so that the union `M c ∪ objFam N` is pseudorandom with an error that does not
pay for the vertices of the seeds. -/
def shiftFam {n D K : ℕ} (I : Fin K → Finset (Fin D)) (M : Fin D → Set (Set (Fin n)))
    (k : Fin K) (base : Set (Set (Fin n))) : Set (Set (Fin n)) :=
  {A | ∃ X ∈ base, ∃ c : Fin D, c ∈ I k ∧ A = X \ famVert (M c)}

theorem mem_shiftFam {n D K : ℕ} {I : Fin K → Finset (Fin D)} {M : Fin D → Set (Set (Fin n))}
    {k : Fin K} {base : Set (Set (Fin n))} {A : Set (Fin n)} :
    A ∈ shiftFam I M k base ↔ ∃ X ∈ base, ∃ c : Fin D, c ∈ I k ∧ A = X \ famVert (M c) :=
  Iff.rfl

/-- **The pseudorandomness transfer.**  If the object matching `Nobj` is
`(γp,κ)`-pseudorandom with respect to all the *shifted* sets `X ∖ V(M c)`
(`X` in `base`), then `M c ∪ objFam Nobj` is `(γp, κ + γp σ/n)`-pseudorandom with
respect to `base`, where `σ` bounds the number of vertices of the seed. -/
theorem pseudoRandom_union {n D : ℕ} (hn : 1 ≤ n) {𝓜 : MultiHypergraph n}
    {M : Fin D → Set (Set (Fin n))} {Nobj : Set (EdgeObj 𝓜)}
    {base 𝓕V : Set (Set (Fin n))} {γp κ σ : ℝ} (c : Fin D)
    (hγp0 : 0 ≤ γp) (hσ0 : 0 ≤ σ)
    (hsub : ∀ X ∈ base, X \ famVert (M c) ∈ 𝓕V)
    (hP : PseudoRandomFam (objFam Nobj) 𝓕V γp κ)
    (hsize : ((famVert (M c)).ncard : ℝ) ≤ σ) :
    PseudoRandomFam (M c ∪ objFam Nobj) base γp (κ + γp * σ / (n : ℝ)) := by
  intro X hX
  have hP' := hP _ (hsub X hX)
  have hA : |(((X \ famVert (M c)) \ objVert Nobj).ncard : ℝ)
      - γp * ((X \ famVert (M c)).ncard : ℝ)| ≤ κ * (n : ℝ) := by
    simpa only [famVert_objFam] using hP'
  have hgoal : X \ famVert (M c ∪ objFam Nobj) = (X \ famVert (M c)) \ objVert Nobj := by
    rw [famVert_union, famVert_objFam]
    ext y
    simp only [Set.mem_sdiff, Set.mem_union]
    tauto
  rw [hgoal]
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcap : ((X ∩ famVert (M c)).ncard : ℝ) ≤ σ :=
    le_trans (by exact_mod_cast Set.ncard_le_ncard Set.inter_subset_right (Set.toFinite _)) hsize
  have hdiff : (((X \ famVert (M c)).ncard : ℕ) : ℝ)
      = (X.ncard : ℝ) - ((X ∩ famVert (M c)).ncard : ℝ) := by
    have h1 : X \ (X ∩ famVert (M c)) = X \ famVert (M c) := by
      ext y; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto
    have h2 := Set.ncard_sdiff (s := X ∩ famVert (M c)) (t := X) Set.inter_subset_left
    have h3 : (((X \ (X ∩ famVert (M c))).ncard : ℕ) : ℝ)
        = (X.ncard : ℝ) - ((X ∩ famVert (M c)).ncard : ℝ) := by
      rw [h2, Nat.cast_sub (Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _))]
    rwa [h1] at h3
  have hlow : ((X.ncard : ℝ)) - σ ≤ ((X \ famVert (M c)).ncard : ℝ) := by
    rw [hdiff]; linarith
  have hup : ((X \ famVert (M c)).ncard : ℝ) ≤ (X.ncard : ℝ) := by
    rw [hdiff]; linarith [hcap]
  have hmul : (κ + γp * σ / (n : ℝ)) * (n : ℝ) = κ * (n : ℝ) + γp * σ := by
    field_simp
  rw [abs_le] at hA ⊢
  constructor
  · nlinarith [hA.1, hlow, hγp0, hmul]
  · nlinarith [hA.2, hup, hγp0, hσ0, hmul]

/-! ## The absorber after deleting the used edges -/

theorem isAbsorber_delete_gamma {n : ℕ} {G' R Rcur : Hypergraph (Fin n)}
    {𝓥 : Set (Set (Fin n))} {ρ γ γabs α ξ : ℝ} (h : IsAbsorber G' R 𝓥 ρ γ ξ)
    (hsub : Rcur ⊆ R) (hΔ : ∀ v : Fin n, (degAt (R \ Rcur) v : ℝ) ≤ α * (n : ℝ))
    (hγα : γ + α ≤ γabs) : IsAbsorber G' Rcur 𝓥 ρ γabs ξ :=
  (h.delete hsub hΔ).mono_gamma hγα

/-! ## The absorption step -/

/-- **One batch of the §7 assembly's absorption.**  A batch of `≤ κa n`
edge-disjoint matchings, pseudorandom with respect to `𝓕(R) ∪ {U,S,∅}`, is
extended by edges of `R` so that the coverage of `U` is perfect (if `U` is
small) or nearly perfect with defects in `S`. -/
theorem absorbBatch {n : ℕ} {K' : ℕ} {𝓗 : MultiHypergraph n} {R Rcur : Hypergraph (Fin n)}
    {𝓥 : Set (Set (Fin n))} {U S : Set (Fin n)} {ρ ε γp κa ξ : ℝ}
    (hm : InternalMargins n ρ ε γp κa ξ) (hc : CrossingMargins n ρ ε γp κa ξ)
    (hR2 : ∀ e ∈ Rcur, edgeSize e = 2)
    (habs : IsAbsorber (incidentTwo (MultiHypergraph.pow2 𝓗) U) Rcur 𝓥 ρ (10 * γp) ξ)
    (hU𝓥 : U ∈ 𝓥)
    (hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤
      (degAt (incidentTwo (MultiHypergraph.pow2 𝓗) U) u : ℝ))
    (hSsub : S ⊆ U) (hS : γp * (n : ℝ) ≤ (S.ncard : ℝ))
    (N : Fin K' → Set (Set (Fin n)))
    (hNmat : ∀ i, MultiHypergraph.IsMatching 𝓗 (N i))
    (hNdisj : ∀ i j, i ≠ j → EdgeDisjointFam (N i) (N j))
    (hNR : ∀ i, ∀ e ∈ N i, e ∉ Rcur)
    (hpseudo : ∀ i, PseudoRandomFam (N i) (absorbFam Rcur U S) γp κa)
    (hk : (K' : ℝ) ≤ κa * (n : ℝ)) :
    ∃ N' : Fin K' → Set (Set (Fin n)),
      (∀ i, N i ⊆ N' i) ∧
      (∀ i, ∀ e ∈ N' i, e ∉ N i → e ∈ Rcur) ∧
      (∀ i, MultiHypergraph.IsMatching 𝓗 (N' i)) ∧
      (∀ i j, i ≠ j → EdgeDisjointFam (N' i) (N' j)) ∧
      (((U.ncard : ℝ) ≤ (1 - 2 * ε) * (n : ℝ)) → ∀ i, CoversFamMulti (N' i) U) ∧
      (((1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ)) → NearlyPerfectCoverageFam N' U S) := by
  by_cases hsmall : (U.ncard : ℝ) ≤ (n : ℝ) / 100
  · obtain ⟨N', h1, h2, h3, h4, h5⟩ :=
      crossing_absorption_multi (𝓜 := 𝓗) (R := Rcur) (𝓥 := 𝓥) (U := U)
        (ρ := ρ) (ε := ε) (γ := γp) (κ := κa) (ξ := ξ)
        hc hsmall hUdeg habs hU𝓥 N hNmat hNdisj hNR
        (fun i => (hpseudo i).mono (absorbFam_subset_crossing Rcur U S)) hk
    refine ⟨N', h1, h2, h3, h4, ?_, ?_⟩
    · intro _ i
      exact h5 i
    · intro _
      refine ⟨?_, ?_, ?_⟩
      · intro u hu
        have : ({i : Fin K' | u ∈ famVert (N' i)} : Set (Fin K')) = Set.univ := by
          ext i; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact h5 i hu
        rw [this]
        simp
      · intro i x hx
        exact absurd (h5 i hx.1) hx.2
      · intro i
        have hemp : U \ famVert (N' i) = ∅ :=
          Set.eq_empty_iff_forall_notMem.mpr (fun x hx => hx.2 (h5 i hx.1))
        rw [hemp, Set.ncard_empty]
        norm_num
  · have hgt : (n : ℝ) / 100 < (U.ncard : ℝ) := not_le.mp hsmall
    have hB0 : ((0:ℕ):ℝ) ≤ ρ ^ 2 * (γp * (n:ℝ)) / 400 := by
      rw [Nat.cast_zero]
      apply div_nonneg
      · exact mul_nonneg (sq_nonneg ρ) (mul_nonneg (le_of_lt hm.hγ) (Nat.cast_nonneg n))
      · norm_num
    obtain ⟨N', h1, h2, h3, h4, h5, h6⟩ :=
      internal_absorption_multi (𝓜 := 𝓗) (R := Rcur) (𝓥 := 𝓥) (U := U) (S := S)
        (ρ := ρ) (ε := ε) (γ := γp) (κ := κa) (ξ := ξ) (B := 0)
        hm (internalMatchingInput n 0) (le_of_lt hgt) hUdeg habs hU𝓥 hR2 hB0 hS hSsub
        N hNmat hNdisj hNR
        (fun i => (hpseudo i).mono (absorbFam_subset_internal Rcur U S)) hk
    exact ⟨N', h1, h2, h3, h4, h5, h6⟩


/-! ## The batches: colours served by the first `j` parts -/

/-- The colours served by the batches `0, …, j-1`. -/
def Proc {D K : ℕ} (I : Fin K → Finset (Fin D)) (j : ℕ) : Finset (Fin D) :=
  Finset.univ.filter (fun c => ∃ k : Fin K, k.val < j ∧ c ∈ I k)

/-- The parts `0, …, j-1`. -/
def procParts (K : ℕ) (j : ℕ) : Finset (Fin K) :=
  Finset.univ.filter (fun k => k.val < j)

theorem mem_Proc {D K : ℕ} {I : Fin K → Finset (Fin D)} {j : ℕ} {c : Fin D} :
    c ∈ Proc I j ↔ ∃ k : Fin K, k.val < j ∧ c ∈ I k := by
  simp [Proc]

theorem mem_procParts {K j : ℕ} {k : Fin K} : k ∈ procParts K j ↔ k.val < j := by
  simp [procParts]

theorem Proc_mono {D K : ℕ} {I : Fin K → Finset (Fin D)} {j j' : ℕ} (h : j ≤ j') :
    Proc I j ⊆ Proc I j' := by
  intro c hc
  rw [mem_Proc] at hc ⊢
  obtain ⟨k, hk, hck⟩ := hc
  exact ⟨k, lt_of_lt_of_le hk h, hck⟩

theorem Proc_succ {D K : ℕ} (I : Fin K → Finset (Fin D)) {j : ℕ} (hj : j < K) :
    Proc I (j + 1) = Proc I j ∪ I ⟨j, hj⟩ := by
  ext c
  rw [mem_Proc, Finset.mem_union, mem_Proc]
  constructor
  · rintro ⟨k, hk, hck⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
    · exact Or.inl ⟨k, h, hck⟩
    · have hk' : k = ⟨j, hj⟩ := Fin.ext h
      exact Or.inr (by rw [← hk']; exact hck)
  · rintro (⟨k, hk, hck⟩ | hc)
    · exact ⟨k, Nat.lt_succ_of_lt hk, hck⟩
    · exact ⟨⟨j, hj⟩, Nat.lt_succ_self j, hc⟩

theorem procParts_mono {K : ℕ} {j j' : ℕ} (h : j ≤ j') :
    procParts K j ⊆ procParts K j' := by
  intro k hk
  rw [mem_procParts] at hk ⊢
  exact lt_of_lt_of_le hk h

theorem procParts_succ {K : ℕ} {j : ℕ} (hj : j < K) :
    procParts K (j + 1) = insert ⟨j, hj⟩ (procParts K j) := by
  ext k
  rw [mem_procParts, Finset.mem_insert, mem_procParts]
  constructor
  · intro hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
    · exact Or.inr h
    · exact Or.inl (Fin.ext h)
  · rintro (h | h)
    · rw [h]; exact Nat.lt_succ_self j
    · exact Nat.lt_succ_of_lt h

/-- The total singleton multiplicity of the processed parts at `w`. -/
def asmSinglesSum {n K : ℕ} (𝓗' : MultiHypergraph n) (P : EdgePartition 𝓗' K) (j : ℕ)
    (w : Fin n) : ℝ :=
  ∑ k ∈ procParts K j, ((P.part k).singles w : ℝ)

/-- **The §7 assembly invariant.**  After the batches `0, …, j-1` have been
served, `Nf` is the family of the colour classes built so far. -/
def Inv {n D K : ℕ} (𝓗 𝓗' : MultiHypergraph n) (R : Hypergraph (Fin n))
    (U S : Set (Fin n)) (M : Fin D → Set (Set (Fin n))) (I : Fin K → Finset (Fin D))
    (P : EdgePartition 𝓗' K) (κ γp ε : ℝ) (j : ℕ)
    (Nf : Fin D → Set (Set (Fin n))) : Prop := by
  classical
  exact
  -- (a) unprocessed colours are the seeds
  ((∀ c, c ∉ Proc I j → Nf c = M c) ∧
  -- (b) processed colours contain the seeds, are matchings, and only add
  --     𝓗'-edges or R-edges
  (∀ c ∈ Proc I j, M c ⊆ Nf c ∧ MultiHypergraph.IsMatching 𝓗 (Nf c) ∧
    (∀ e ∈ Nf c, e ∉ M c →
      e ∈ R ∨ ∃ k ∈ procParts K j, c ∈ I k ∧ e ∈ (P.part k).edgeSet)) ∧
  -- (c) pairwise edge-disjointness
  (∀ c c', c ≠ c' → EdgeDisjointFam (Nf c) (Nf c')) ∧
  -- (d) the R-edges used through a vertex
  (∀ w, ((({e ∈ R | w ∈ e} ∩ (⋃ c ∈ Proc I j, Nf c)) : Set (Set (Fin n))).ncard : ℝ)
      ≤ (γp + 2 * κ) * ((Proc I j).card : ℝ)) ∧
  -- (e) the leftover edges of the processed parts
  (∀ k ∈ procParts K j, ∀ w,
      ((({e ∈ (P.part k).edgeSet | w ∈ e} \ (⋃ c ∈ I k, Nf c)) : Set (Set (Fin n))).ncard : ℝ)
        ≤ (γp + 2 * κ) * ((I k).card : ℝ)) ∧
  -- (f) the coverage of `U`
  ((((1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ)) →
      (∀ u ∈ U, ((({c ∈ Proc I j | u ∈ famVert (Nf c)}) : Set (Fin D)).ncard : ℝ) + 1
          ≥ ((Proc I j).card : ℝ)) ∧
      (∀ c ∈ Proc I j, U \ famVert (Nf c) ⊆ S) ∧
      (∀ c ∈ Proc I j, (U \ famVert (Nf c)).ncard ≤ 1)) ∧
   (¬ ((1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ)) →
      ∀ c ∈ Proc I j, CoversFamMulti (Nf c) U)) ∧
  -- (g) the singleton bookkeeping
  (∀ w, ((((Proc I j).filter (fun c => ({w} : Set (Fin n)) ∈ Nf c ∧
        ({w} : Set (Fin n)) ∉ M c)).card : ℝ)
      ≤ asmSinglesSum 𝓗' P j w)))


/-- The union bound for `ncard` over a finite index type, in `ℝ`. -/
theorem ncard_iUnion_le_sumR {ι α : Type*} [Fintype ι] (f : ι → Set α) (b : ι → ℝ)
    (h : ∀ i, ((f i).ncard : ℝ) ≤ b i) :
    (((⋃ i, f i).ncard : ℕ) : ℝ) ≤ ∑ i, b i := by
  classical
  have h2 : ∀ t : Finset ι, (((⋃ i ∈ (t : Set ι), f i).ncard : ℕ) : ℝ) ≤ ∑ i ∈ t, b i := by
    intro t
    induction t using Finset.induction with
    | empty => simp
    | insert a t ha ih =>
      have hsplit : (⋃ i ∈ (((insert a t : Finset ι)) : Set ι), f i)
          = f a ∪ (⋃ i ∈ (t : Set ι), f i) := by
        ext x
        simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_insert, Set.mem_union]
        constructor
        · rintro ⟨i, h | h, hx⟩
          · rw [h] at hx; exact Or.inl hx
          · exact Or.inr ⟨i, h, hx⟩
        · rintro (hx | ⟨i, hi, hx⟩)
          · exact ⟨a, Or.inl rfl, hx⟩
          · exact ⟨i, Or.inr hi, hx⟩
      rw [hsplit, Finset.sum_insert ha]
      have h1 := Set.ncard_union_le (f a) (⋃ i ∈ (t : Set ι), f i)
      have h5 : ((f a).ncard : ℝ) ≤ b a := h a
      have h4 : (((⋃ i ∈ (t : Set ι), f i).ncard : ℕ) : ℝ) ≤ ∑ i ∈ t, b i := ih
      have h6 : (((f a ∪ (⋃ i ∈ (t : Set ι), f i)).ncard : ℕ) : ℝ)
          ≤ ((f a).ncard : ℝ) + (((⋃ i ∈ (t : Set ι), f i).ncard : ℕ) : ℝ) := by
        exact_mod_cast h1
      linarith
  have h2' := h2 (Finset.univ : Finset ι)
  simpa using h2'



/-- `ncard` of a disjoint finite union. -/
theorem ncard_iUnion_disjoint {ι α : Type*} [Fintype ι] [Finite α] (f : ι → Set α)
    (h : ∀ i j, i ≠ j → Disjoint (f i) (f j)) :
    (⋃ i, f i).ncard = ∑ i, (f i).ncard := by
  classical
  have h2 : ∀ s : Finset ι, (⋃ i ∈ s, f i).ncard = ∑ i ∈ s, (f i).ncard := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a t ha ih =>
      have hsplit : (⋃ i ∈ insert a t, f i) = f a ∪ (⋃ i ∈ t, f i) := by
        ext x
        simp only [Set.mem_iUnion, Finset.mem_insert, exists_prop, Set.mem_union]
        constructor
        · rintro ⟨i, h | h, hx⟩
          · subst h; exact Or.inl hx
          · exact Or.inr ⟨i, h, hx⟩
        · rintro (hx | ⟨i, hi, hx⟩)
          · exact ⟨a, Or.inl rfl, hx⟩
          · exact ⟨i, Or.inr hi, hx⟩
      rw [hsplit, Finset.sum_insert ha]
      have hdisj : Disjoint (f a) (⋃ i ∈ t, f i) := by
        rw [Set.disjoint_left]
        intro x hx hy
        simp only [Set.mem_iUnion, exists_prop] at hy
        obtain ⟨i, hi, hiy⟩ := hy
        exact (Set.disjoint_left.mp (h a i (by rintro rfl; exact ha hi))) hx hiy
      rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), ih]
  have h3 := h2 (Finset.univ : Finset ι)
  simpa using h3

/-- The proper edges through `v` are partitioned among the parts, so the
degrees add up. -/
theorem hdeg_parts_sum {n K : ℕ} {𝓗' : MultiHypergraph n} (P : EdgePartition 𝓗' K)
    (v : Fin n) :
    (∑ k : Fin K, MultiHypergraph.hdeg (P.part k).edges v)
      = MultiHypergraph.hdeg 𝓗'.edges v := by
  classical
  have hunion : (⋃ k : Fin K, ({e ∈ (P.part k).edges | v ∈ e} : Set (Set (Fin n))))
      = {e ∈ 𝓗'.edges | v ∈ e} := by
    ext e
    constructor
    · intro he
      rw [Set.mem_iUnion] at he
      obtain ⟨k, hk⟩ := he
      exact ⟨(P.le k).1 hk.1, hk.2⟩
    · intro he
      obtain ⟨heE, hve⟩ := he
      obtain ⟨k, hk, -⟩ := P.edges_cover e heE
      exact Set.mem_iUnion.mpr ⟨k, hk, hve⟩
  have hdisj : ∀ k k' : Fin K, k ≠ k' →
      Disjoint ({e ∈ (P.part k).edges | v ∈ e} : Set (Set (Fin n)))
        ({e ∈ (P.part k').edges | v ∈ e} : Set (Set (Fin n))) := by
    intro k k' hkk
    rw [Set.disjoint_left]
    rintro e ⟨hek, -⟩ ⟨hek', -⟩
    obtain ⟨k0, hk0, huniq⟩ := P.edges_cover e ((P.le k).1 hek)
    exact hkk (by rw [huniq k hek, huniq k' hek'])
  have h1 : (⋃ k : Fin K, ({e ∈ (P.part k).edges | v ∈ e} : Set (Set (Fin n)))).ncard
      = ∑ k : Fin K, ({e ∈ (P.part k).edges | v ∈ e} : Set (Set (Fin n))).ncard :=
    ncard_iUnion_disjoint _ hdisj
  have h2 : ({e ∈ 𝓗'.edges | v ∈ e} : Set (Set (Fin n))).ncard
      = ∑ k : Fin K, MultiHypergraph.hdeg (P.part k).edges v := by
    rw [← hunion]
    exact h1
  have h3 : (∑ k : Fin K, MultiHypergraph.hdeg (P.part k).edges v)
      = ({e ∈ 𝓗'.edges | v ∈ e} : Set (Set (Fin n))).ncard := h2.symm
  simpa only [MultiHypergraph.hdeg] using h3

/-- The singleton multiplicities of the parts sum to the multiplicity of `𝓗'`. -/
theorem singles_parts_sum {n K : ℕ} {𝓗' : MultiHypergraph n} (P : EdgePartition 𝓗' K)
    (v : Fin n) :
    (∑ k : Fin K, (P.part k).singles v) = 𝓗'.singles v := by
  classical
  have hkey : (∑ k : Fin K, (P.part k).deg v)
      = (∑ k : Fin K, MultiHypergraph.hdeg (P.part k).edges v)
        + (∑ k : Fin K, (P.part k).singles v) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => (MultiHypergraph.deg_def (P.part k) v).symm)
  have h1 : (∑ k : Fin K, (P.part k).deg v) = 𝓗'.deg v := P.deg_sum v
  have h2 := hdeg_parts_sum P v
  have h3 : 𝓗'.deg v = MultiHypergraph.hdeg 𝓗'.edges v + 𝓗'.singles v :=
    MultiHypergraph.deg_def 𝓗' v
  omega

theorem procParts_self (K : ℕ) : procParts K K = Finset.univ := by
  ext k
  rw [mem_procParts]
  simp

theorem asmSinglesSum_eq {n K : ℕ} {𝓗' : MultiHypergraph n} (P : EdgePartition 𝓗' K)
    (v : Fin n) : asmSinglesSum 𝓗' P K v = (𝓗'.singles v : ℝ) := by
  classical
  have h1 : (∑ k : Fin K, (P.part k).singles v) = 𝓗'.singles v := singles_parts_sum P v
  have h2 : asmSinglesSum 𝓗' P K v = ((∑ k : Fin K, (P.part k).singles v : ℕ) : ℝ) := by
    rw [asmSinglesSum, procParts_self]
    push_cast
    rfl
  rw [h2]
  exact_mod_cast h1

end

end Work.Deep.Nibble
