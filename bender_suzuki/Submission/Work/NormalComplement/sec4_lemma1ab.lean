import Mathlib
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.appI_four
import Submission.Work.NormalComplement.appI_one
import Submission.Work.NormalComplement.sec4_lemma1ab_lemma3

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

/-- `V = C_D(t)` normalises the set `K = J(D,t)`: App. I (4) applied with `d = 2` to `X = D`
(`D = twoPoint H t` has odd order, and `Kapp t D = Kset D t` there). -/
theorem centD_normalizes_Kset {G : Type} [Group G] [Finite G] {H : Subgroup G} {t : G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) (ht : orderOf t = 2) (htH : t ∉ H) :
    ∀ k ∈ Kset (Submission.Blueprint.twoPoint H t) t,
      ∀ v ∈ Submission.Blueprint.centD H t,
        v * k * v⁻¹ ∈ Kset (Submission.Blueprint.twoPoint H t) t := by
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h; simpa [pow_two] using h
  have hoddD : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) := hH.2.2 t htH
  have hcopD : Nat.Coprime (Nat.card ↥(Submission.Blueprint.twoPoint H t)) 2 :=
    Nat.coprime_two_right.mpr hoddD
  have htD : NormalizedBy t (Submission.Blueprint.twoPoint H t) := by
    intro x hx
    refine ⟨?_, Subgroup.mem_map.mpr ⟨x, hx.1, rfl⟩⟩
    obtain ⟨h, hh, hxh⟩ := Subgroup.mem_map.mp hx.2
    have hxt : x = t * h * t⁻¹ := by rw [← hxh]; rfl
    have hmem : t * x * t⁻¹ = h := by
      rw [hxt, inv_eq_of_mul_eq_one_right ht2]
      calc t * (t * h * t) * t = (t * t) * h * (t * t) := by group
        _ = h := by rw [ht2]; simp
    rw [hmem]
    exact hh
  obtain ⟨-, hKapp, -, -, -, -, -⟩ := appI_four (d := 2) Nat.prime_two ht htD hcopD
  obtain ⟨-, hKappKset⟩ := appI_one (d := 2) Nat.prime_two ht htD hcopD
  have hKappKset' : Kapp t (Submission.Blueprint.twoPoint H t) =
      Kset (Submission.Blueprint.twoPoint H t) t := (hKappKset rfl).1
  intro k hk v hv
  rw [← hKappKset'] at hk ⊢
  exact hKapp k hk v ⟨hv.2, hv.1⟩

/-- **Peterfalvi I Ch. III §4 Lemma 1 (a),(b)** (p.179): from `Setup45` (a prime `p ∣ |E:E'|` with
`1 ≠ P ≤ E ⊓ V` fixed-point-free on `K`) there is `A` with `Setup45A`, i.e. `V = A ⋊ P` with
`A ≠ 1`, `|C_K(A)| = 2^p - 1`, and `C_K(B) = C_K(A)` for every `P`-invariant `1 ≠ B ≤ A`.
Route in `_design/Sec4.lean`; needs the full `sec1_lemma3` (twice: with `X` the `X` of (D2), then
with `B`), which may be imported from `Work.NormalComplement.sec1_lemma3`, or inlined. -/
theorem sec4_lemma1ab (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hMod : Submission.Blueprint.ModelFactsProp)
    (hV : Work.NormalComplement.AppVProp) {G : Type} [Group G] [Finite G] {H : Subgroup G}
    {t : G} {W : Subgroup G} {p : ℕ} {P : Subgroup G}
    (h : Work.NormalComplement.Design.Setup45 G H t W p P) :
    ∃ A : Subgroup G, Work.NormalComplement.Design.Setup45A G H t W p P A := by
  classical
  -- App. I (4): `V` normalises `Kset D t`.
  have hVK := centD_normalizes_Kset h.se h.invol h.notMem
  -- (D2): choose `1 ≠ X ⊴ V` with `N_K(X) ≠ 1`.
  obtain ⟨⟨X, hXne, hXV, hXN, k, hkK, hk1, hkcent⟩, -, -⟩ := h.d2
  have hkCX : k ∈ Subgroup.centralizer (X : Set G) := by
    intro x hx
    have h := hkcent x hx
    calc x * k = (k * x * k⁻¹) * k := by rw [h]
      _ = k * x := by group
  have hkNKX : k ∈ Design.NK H t X :=
    ⟨hkK, Subgroup.centralizer_le_normalizer (X : Set G) hkCX⟩
  have hNKX : ∃ kk ∈ Design.NK H t X, kk ≠ 1 := ⟨k, hkNKX, hk1⟩
  have hNKXCK : Design.NK H t X = Design.CK H t X ∧
      (Design.CK H t X).ncard = 2 ^ Nat.card P - 1 ∧
      (Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G) ⊓
          Subgroup.centralizer (Design.NK H t X)) ⊓ P = ⊥ ∧
      (Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G) ⊓
          Subgroup.centralizer (Design.NK H t X)) ⊔ P =
        Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G) :=
    sec4_lemma1ab_lemma3 hFT hC4 hMod hV h.sit h.se h.invol h.notMem hXne hXV hNKX
      (by
        intro hbot
        have h1 : Nat.card ↥P = 1 := by rw [hbot]; exact Subgroup.card_bot
        rw [h.P_card] at h1
        exact h.prime.ne_one h1)
      (h.P_le.trans inf_le_right) ((h.P_le.trans inf_le_right).trans hXN)
      (by
        intro x hxP hx1 kk hkk
        exact h.P_fpf x hxP hx1 kk
          (show kk ∈ Kset (Submission.Blueprint.twoPoint H t) t from
            (show kk ∈ Kset (Submission.Blueprint.twoPoint H t) t ∩
                (Subgroup.normalizer (X : Set G) : Set G) from hkk).1))
  obtain ⟨hNKeqCK, -, hinfX, hsupX⟩ := hNKXCK
  -- `X ⊴ V`, so `N_V(X) = V`.
  have hVN : Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G) =
      Submission.Blueprint.centD H t :=
    le_antisymm inf_le_left (le_inf le_rfl hXN)
  -- the candidate `A = C_V(N_K(X))`.
  let A : Subgroup G :=
    Submission.Blueprint.centD H t ⊓ Subgroup.centralizer (Design.NK H t X : Set G)
  have hAsup : A ⊔ P = Submission.Blueprint.centD H t := by
    have hh := hsupX; rw [hVN] at hh; exact hh
  have hAinf : A ⊓ P = ⊥ := by
    have hh := hinfX; rw [hVN] at hh; exact hh
  -- `X ≤ A`, because `x ∈ X` commutes with the elements of `N_K(X) = C_K(X)`.
  have hkCentersA : ∀ n ∈ A, n * k = k * n := by
    intro n hn
    have hnC : n ∈ Subgroup.centralizer (Design.NK H t X : Set G) := hn.2
    exact ((Subgroup.mem_centralizer_iff.mp hnC) k hkNKX).symm
  have hXA : X ≤ A := by
    intro x hx
    refine ⟨hXV hx, ?_⟩
    intro kk hkk
    have hkk' : kk ∈ Design.CK H t X := by rw [← hNKeqCK]; exact hkk
    exact ((Subgroup.mem_centralizer_iff.mp
      (show kk ∈ Subgroup.centralizer (X : Set G) from
        (show kk ∈ Kset (Submission.Blueprint.twoPoint H t) t ∩
            (Subgroup.centralizer (X : Set G) : Set G) from hkk').2)) x hx).symm
  have hAne : A ≠ ⊥ := by
    intro hbot
    have hle : X ≤ (⊥ : Subgroup G) := hbot ▸ hXA
    exact hXne (le_bot_iff.mp hle)
  have hAle : A ≤ Submission.Blueprint.centD H t := inf_le_left
  -- `V ≤ N(A)`: `V`-conjugation fixes the set `N_K(X)` (App. I (4)) and hence `A`.
  have hNKconj : ∀ u ∈ Submission.Blueprint.centD H t, ∀ kk ∈ Design.NK H t X,
      u * kk * u⁻¹ ∈ Design.NK H t X := by
    intro u hu kk hkk
    have hkkK : kk ∈ Kset (Submission.Blueprint.twoPoint H t) t :=
      (show kk ∈ Kset (Submission.Blueprint.twoPoint H t) t ∩
          (Subgroup.normalizer (X : Set G) : Set G) from hkk).1
    have hkkN : kk ∈ Subgroup.normalizer (X : Set G) :=
      (show kk ∈ Kset (Submission.Blueprint.twoPoint H t) t ∩
          (Subgroup.normalizer (X : Set G) : Set G) from hkk).2
    have huN : u ∈ Subgroup.normalizer (X : Set G) := hXN hu
    refine ⟨hVK kk hkkK u hu, ?_⟩
    exact (Subgroup.normalizer (X : Set G)).mul_mem
      ((Subgroup.normalizer (X : Set G)).mul_mem huN hkkN)
      ((Subgroup.normalizer (X : Set G)).inv_mem huN)
  have hconjA : ∀ u ∈ Submission.Blueprint.centD H t, ∀ n ∈ A, u * n * u⁻¹ ∈ A := by
    intro u hu n hn
    refine ⟨(Submission.Blueprint.centD H t).mul_mem
        ((Submission.Blueprint.centD H t).mul_mem hu hn.1)
        ((Submission.Blueprint.centD H t).inv_mem hu), ?_⟩
    intro kk hkk
    have hstep : u⁻¹ * kk * u ∈ Design.NK H t X := by
      have hst := hNKconj u⁻¹ ((Submission.Blueprint.centD H t).inv_mem hu) kk hkk
      simpa using hst
    have hcomm := hn.2 (u⁻¹ * kk * u) hstep
    calc kk * (u * n * u⁻¹) = u * ((u⁻¹ * kk * u) * n) * u⁻¹ := by group
      _ = u * (n * (u⁻¹ * kk * u)) * u⁻¹ := by rw [hcomm]
      _ = (u * n * u⁻¹) * kk := by group
  have hAnormal : Submission.Blueprint.centD H t ≤ Subgroup.normalizer (A : Set G) := by
    intro v hv n
    constructor
    · intro hn; exact hconjA v hv n hn
    · intro hn
      have hmem : v⁻¹ * (v * n * v⁻¹) * v ∈ A := by
        have hmm := hconjA v⁻¹ ((Submission.Blueprint.centD H t).inv_mem hv) (v * n * v⁻¹) hn
        simpa using hmm
      have heq : v⁻¹ * (v * n * v⁻¹) * v = n := by group
      rwa [heq] at hmem
  -- `N_K(A) ≠ 1` (witness `k`, which centralises `A`).
  have hkCentersA' : k ∈ Subgroup.centralizer (A : Set G) := fun n hn => hkCentersA n hn
  have hNKA : ∃ kk ∈ Design.NK H t A, kk ≠ 1 :=
    ⟨k, ⟨hkK, Subgroup.centralizer_le_normalizer (A : Set G) hkCentersA'⟩, hk1⟩
  have hPXA : P ≤ Subgroup.normalizer (A : Set G) :=
    (h.P_le.trans inf_le_right).trans hAnormal
  have hCKAcard : (Design.CK H t A).ncard = 2 ^ p - 1 := by
    have hh := (sec4_lemma1ab_lemma3 hFT hC4 hMod hV h.sit h.se h.invol h.notMem hAne hAle
      hNKA
      (by
        intro hbot
        have h1 : Nat.card ↥P = 1 := by rw [hbot]; exact Subgroup.card_bot
        rw [h.P_card] at h1
        exact h.prime.ne_one h1)
      (h.P_le.trans inf_le_right) hPXA
      (by
        intro x hxP hx1 kk hkk
        exact h.P_fpf x hxP hx1 kk
          (show kk ∈ Kset (Submission.Blueprint.twoPoint H t) t from
            (show kk ∈ Kset (Submission.Blueprint.twoPoint H t) t ∩
                (Subgroup.normalizer (A : Set G) : Set G) from hkk).1))).2.1
    rwa [h.P_card] at hh
  -- (b): for `P`-invariant `1 ≠ B ≤ A`, `C_K(B) = C_K(A)`.
  have hAB : ∀ B : Subgroup G, B ≠ ⊥ → B ≤ A →
      P ≤ Subgroup.normalizer (B : Set G) → Design.CK H t B = Design.CK H t A := by
    intro B hBne hBA hPB
    have hBV : B ≤ Submission.Blueprint.centD H t := hBA.trans hAle
    have hkCentersB : k ∈ Subgroup.centralizer (B : Set G) := fun n hn => hkCentersA n (hBA hn)
    have hNKB : ∃ kk ∈ Design.NK H t B, kk ≠ 1 :=
      ⟨k, ⟨hkK, Subgroup.centralizer_le_normalizer (B : Set G) hkCentersB⟩, hk1⟩
    have hCKBcard : (Design.CK H t B).ncard = 2 ^ p - 1 := by
      have hh := (sec4_lemma1ab_lemma3 hFT hC4 hMod hV h.sit h.se h.invol h.notMem hBne hBV
        hNKB
        (by
          intro hbot
          have h1 : Nat.card ↥P = 1 := by rw [hbot]; exact Subgroup.card_bot
          rw [h.P_card] at h1
          exact h.prime.ne_one h1)
        (h.P_le.trans inf_le_right) hPB
        (by
          intro x hxP hx1 kk hkk
          exact h.P_fpf x hxP hx1 kk
            (show kk ∈ Kset (Submission.Blueprint.twoPoint H t) t from
              (show kk ∈ Kset (Submission.Blueprint.twoPoint H t) t ∩
                  (Subgroup.normalizer (B : Set G) : Set G) from hkk).1))).2.1
      rwa [h.P_card] at hh
    have hsub : Design.CK H t A ⊆ Design.CK H t B := by
      intro kk hkk
      exact ⟨hkk.1, fun n hn => hkk.2 n (hBA hn)⟩
    exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hCKBcard, hCKAcard])).symm
  exact ⟨A, h, hAne, hAle, hAnormal, hAinf, hAsup, hCKAcard, hAB⟩

end Work.NormalComplement
