/-
Design pass 16 (lead), area BG: Bender–Glauberman 1981, Theorems A, B, C.
Contract-level layer: the leaves that feed the three contract Props, the pure arithmetic
leaves, and the three assemblies `thmA_of_leaves`, `thmB_of_leaves`, `thmC_of_leaves`
(PROVED here, no `sorry`).  The character-theoretic leaves that produce `KeyBigProp`,
`KeySmallProp`, `ThmCBigProp`, `ThmCSmallProp` are in `Core16Char.lean`.
Routes: `NOTES_LEAD_gw_design16.md`.  Source: BG pp. 200–215 (page images
`Submission/Work/lead_gw_prior/_bgpg-01..16.png`; PDF with text layer
`lead_gw_prior/1-s2.0-0021869381902532-main.pdf`).
-/
import Mathlib
import Submission.Work.GLUE.Defs

namespace Work.GW2.C16

open Work.GW2 Subgroup

/-! ## 1. Group-theoretic leaves (BGData only) -/

/-- **G2.** `|S| = 2n` is a 2-power `≥ 4`, so `n = 2` or `n ≥ 4`; and `|S₀| = n`. -/
def NCasesProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : BGData G),
    (D.n = 2 ∨ 4 ≤ D.n) ∧ Nat.card D.S0 = D.n

/-- **G3.** `|G : H|` is odd (`S ≤ H`), and `k > 0`. -/
def IndexOddProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : BGData G), Odd D.H.index ∧ 0 < D.k

/-- **G4.** For `|S| ≥ 8`, `4 ∣ k` (each `kᵢ` has 2-part exactly `n/2`, BG p. 207 "m divides k"). -/
def FourDvdKProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : BGData G), 4 ≤ D.n → 4 ∣ D.k

/-! ## 2. The two character-theoretic key identities (produced in `Core16Char.lean`) -/

/-- **KEY-BIG** (Lemma 2.5, `|S| ≥ 8`): with `x := φ(1)` (`φ` the non-trivial constituent of
`λ̃₁ = 1_G + φ`), `|G:H|(x-1)² = 2k²x(x+1)`. -/
def KeyBigProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : BGData G), 4 ≤ D.n →
    ∃ x : ℤ, x ≠ 0 ∧ x ≠ -1 ∧
      (D.H.index : ℤ) * (x - 1) ^ 2 = 2 * (D.k : ℤ) ^ 2 * x * (x + 1)

/-- **KEY-SMALL** (§4 end, `|S| = 4`): `(1 - λ₂)* = 1_G + φ₁ + φ₂ + φ₃` with odd degrees
`a, b, c` (`|a| = 1 ⇒ a = 1`), `1 + a + b + c = 0` and `2k²/|G:H| = 1 + 1/a + 1/b + 1/c`. -/
def KeySmallProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : BGData G), D.n = 2 →
    ∃ a b c : ℤ, Odd a ∧ Odd b ∧ Odd c ∧
      (a = 1 ∨ 3 ≤ |a|) ∧ (b = 1 ∨ 3 ≤ |b|) ∧ (c = 1 ∨ 3 ≤ |c|) ∧ 1 + a + b + c = 0 ∧
      (D.H.index : ℤ) * (a * b * c + b * c + a * c + a * b) = 2 * (D.k : ℤ) ^ 2 * (a * b * c)

/-! ## 3. Pure arithmetic leaves (brute-force checked, see notes §6) -/

/-- **AR-BIG.** `8 ∣ x - 1` is forced (2-adic count), so `x ≥ 9` or `x ≤ -7`, and
`2k²/N = (x-1)²/(x(x+1)) ∈ (2/3, 2)`. -/
def ArithBigProp : Prop :=
  ∀ (N k : ℕ) (x : ℤ), Odd N → 0 < k → 4 ∣ k → x ≠ 0 → x ≠ -1 →
    (N : ℤ) * (x - 1) ^ 2 = 2 * (k : ℤ) ^ 2 * x * (x + 1) →
    N < 3 * (2 * k ^ 2) ∧ 2 * k ^ 2 < 3 * N

/-- **AR-SMALL.** At most two of `a, b, c` are negative, and a negative one is `≤ -3`; so
`r := 1 + 1/a + 1/b + 1/c ∈ (1/3, 3)` (max `8/3` at `(1,1,-3)`). -/
def ArithSmallProp : Prop :=
  ∀ (N k : ℕ) (a b c : ℤ), Odd N → Odd a → Odd b → Odd c →
    (a = 1 ∨ 3 ≤ |a|) → (b = 1 ∨ 3 ≤ |b|) → (c = 1 ∨ 3 ≤ |c|) → 1 + a + b + c = 0 →
    (N : ℤ) * (a * b * c + b * c + a * c + a * b) = 2 * (k : ℤ) ^ 2 * (a * b * c) →
    N < 3 * (2 * k ^ 2) ∧ 2 * k ^ 2 < 3 * N

/-! ## 4. Theorem A: assembly (PROVED) -/

theorem thmA_of_leaves (hN : NCasesProp) (hI : IndexOddProp) (h4 : FourDvdKProp)
    (hKB : KeyBigProp) (hKS : KeySmallProp) (hAB : ArithBigProp) (hAS : ArithSmallProp) :
    BGThmAProp := by
  intro G _ _ D
  obtain ⟨hn, -⟩ := hN G D
  obtain ⟨hodd, hk⟩ := hI G D
  rcases hn with hn | hn
  · obtain ⟨a, b, c, ha, hb, hc, ha', hb', hc', hsum, hid⟩ := hKS G D hn
    exact hAS _ _ a b c hodd ha hb hc ha' hb' hc' hsum hid
  · obtain ⟨x, hx0, hx1, hid⟩ := hKB G D hn
    exact hAB _ _ x hodd hk (h4 G D hn) hx0 hx1 hid

/-! ## 5. Theorem B: leaves and assembly (PROVED) -/

/-- **B1.** Restriction of the BG data to a subgroup `G₁ ⊇ H` with one class of involutions:
same `S, S₀, t, t₁, t₂` (`S ≤ H ≤ G₁`), `C_{G₁}(t) = H`, `|G₁ : H|` is the relative index,
and `k` is unchanged (`C_{G₁}(tᵢ) ∩ H = C_H(tᵢ)`). -/
def SubBGDataProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : BGData G) (G1 : Subgroup G), D.H ≤ G1 →
    (∀ x y : G, x ∈ G1 → y ∈ G1 → orderOf x = 2 → orderOf y = 2 →
      ∃ g ∈ G1, g * x * g⁻¹ = y) →
    ∃ D' : BGData ↥G1, D'.H.index = D.H.relIndex G1 ∧ D'.k = D.k

/-- **B2.** `G₁` is strongly embedded (`C(x) ≤ G₁` for every involution `x ∈ G₁`, since
`x ~_{G₁} t` and `C(t) = H ≤ G₁`; hence `G₁ ∩ G₁^g` has odd order for `g ∉ G₁`), so `S`
acts semiregularly on the `|G:G₁| - 1` cosets `≠ G₁`, and `4 ≤ |S|` divides `|G:G₁| - 1`. -/
def StrongEmbedProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : BGData G) (G1 : Subgroup G), G1 ≠ ⊤ → D.H ≤ G1 →
    (∀ x y : G, x ∈ G1 → y ∈ G1 → orderOf x = 2 → orderOf y = 2 →
      ∃ g ∈ G1, g * x * g⁻¹ = y) →
    4 ∣ G1.index - 1

theorem thmB_of_leaves (hA : BGThmAProp) (hSub : SubBGDataProp) (hSE : StrongEmbedProp) :
    BGThmBProp := by
  intro G _ _ D G1 hne hle hcl
  obtain ⟨D', hidx, hk⟩ := hSub G D G1 hle hcl
  have h1 : D.H.index < 3 * (2 * D.k ^ 2) := (hA G D).1
  have h2 : 2 * D'.k ^ 2 < 3 * D'.H.index := (hA (↥G1) D').2
  rw [hidx, hk] at h2
  have hmul : D.H.relIndex G1 * G1.index = D.H.index := Subgroup.relIndex_mul_index hle
  have hHidx : D.H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrel : 0 < D.H.relIndex G1 := by
    rcases Nat.eq_zero_or_pos (D.H.relIndex G1) with h | h
    · rw [h, zero_mul] at hmul; exact absurd hmul.symm hHidx
    · exact h
  have hlt : D.H.relIndex G1 * G1.index < D.H.relIndex G1 * 9 := by
    rw [hmul]; omega
  have h9 : G1.index < 9 := Nat.lt_of_mul_lt_mul_left hlt
  have h0 : G1.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1' : G1.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
  have hd := hSE G D G1 hne hle hcl
  omega

/-! ## 6. Theorem C: case split and assembly (PROVED) -/

/-- **C-BIG** (`|S| ≥ 8`, BG pp. 210–211). -/
def ThmCBigProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : BGData G) (K1 K2 : Subgroup G), 4 ≤ D.n →
    IsMaxInverted D.H D.t1 K1 → IsMaxInverted D.H D.t2 K2 →
    IsInternalDirect D.U (D.B1 ⊓ K2) (D.B ⊔ (K1 ⊓ K2)) →
    Nat.Coprime (Nat.card (K1 ⊓ K2 : Subgroup G)) D.H.index →
    ⁅D.B, D.B⁆ ≠ D.B →
    (D.U ≠ D.B ⊔ (K1 ⊓ K2) → IsFrobeniusWith (D.B ⊔ (K1 ⊓ K2)) (K1 ⊓ K2) D.B) →
    ¬ IsSimpleGroup G

/-- **C-SMALL** (`|S| = 4`, BG pp. 214–215). -/
def ThmCSmallProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : BGData G) (K1 K2 : Subgroup G), D.n = 2 →
    IsMaxInverted D.H D.t1 K1 → IsMaxInverted D.H D.t2 K2 →
    IsInternalDirect D.U (D.B1 ⊓ K2) (D.B ⊔ (K1 ⊓ K2)) →
    Nat.Coprime (Nat.card (K1 ⊓ K2 : Subgroup G)) D.H.index →
    ⁅D.B, D.B⁆ ≠ D.B →
    (D.U ≠ D.B ⊔ (K1 ⊓ K2) → IsFrobeniusWith (D.B ⊔ (K1 ⊓ K2)) (K1 ⊓ K2) D.B) →
    ¬ IsSimpleGroup G

theorem thmC_of_leaves (hN : NCasesProp) (hBig : ThmCBigProp) (hSmall : ThmCSmallProp) :
    BGThmCProp := by
  intro G _ _ D K1 K2 h1 h2 hdir hcop hB hfr
  rcases (hN G D).1 with hn | hn
  · exact hSmall G D K1 K2 hn h1 h2 hdir hcop hB hfr
  · exact hBig G D K1 K2 hn h1 h2 hdir hcop hB hfr

/-! ## 7. Group-theoretic leaves used by the Theorem C chain (statements; routes in notes) -/

/-- **G5.** `|S| = 4`: `k₁ = k₂` (`C_H(tᵢ) = C_G(S)` for both `i`, since `S = ⟨t, tᵢ⟩`). -/
def KEqSmallProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : BGData G), D.n = 2 →
    (centralizer ({D.t1} : Set G)).relIndex D.H = (centralizer ({D.t2} : Set G)).relIndex D.H

/-- **G6.** The §3 hypothesis follows from the hypotheses of Theorem C: `S' = ⟨x² | x ∈ S₀⟩`
centralizes `U` (`B₁ ∩ K₂` is inverted by the generator `t₁t₂` of `S₀`, `B K` is centralized by
`S₀`).  Also `B ⊄ U'` (from `B' ≠ B` and the direct decomposition). -/
def ThmCSec3Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : BGData G) (K1 K2 : Subgroup G),
    IsMaxInverted D.H D.t1 K1 → IsMaxInverted D.H D.t2 K2 →
    IsInternalDirect D.U (D.B1 ⊓ K2) (D.B ⊔ (K1 ⊓ K2)) → ⁅D.B, D.B⁆ ≠ D.B →
    (∀ x ∈ D.S0, ∀ u ∈ D.U, x ^ 2 * u = u * x ^ 2) ∧ ¬ D.B ≤ ⁅D.U, D.U⁆

/-- **G7** (`|S| = 4`, p. 214): `U = B K` and `k = 2|K|`. -/
def ThmCSmallShapeProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : BGData G) (K1 K2 : Subgroup G), D.n = 2 →
    IsMaxInverted D.H D.t1 K1 → IsMaxInverted D.H D.t2 K2 →
    IsInternalDirect D.U (D.B1 ⊓ K2) (D.B ⊔ (K1 ⊓ K2)) →
    D.U = D.B ⊔ (K1 ⊓ K2) ∧ D.k = 2 * Nat.card (K1 ⊓ K2 : Subgroup G)

/-- **G8 = Remark 3.5** (p. 210) in the form used: under the hypotheses of Theorem C with
`G` simple, `K ≠ 1`.  Route: if `K = 1` then `U ≠ BK` is impossible (Frobenius needs
`K ≠ 1`), so `U = B` and `S` centralizes `U`; `G₁ := N_G(B) ⊇ H` has one class of
involutions (fusion of `t₁` to `t` happens in `N_G(V)`, `V = ⟨t, t₁⟩`, and
`N_G(V) ≤ N_G(O(C_G(V))) = N_G(B)`), so Theorem B gives `|G : G₁| = 5`; `G` simple ⇒
`G ↪ A₅`, `G ≅ A₅`, `U = 1`, contradicting `B' ≠ B`. -/
def KNeOneProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : BGData G) (K1 K2 : Subgroup G),
    IsMaxInverted D.H D.t1 K1 → IsMaxInverted D.H D.t2 K2 →
    IsInternalDirect D.U (D.B1 ⊓ K2) (D.B ⊔ (K1 ⊓ K2)) → ⁅D.B, D.B⁆ ≠ D.B →
    (D.U ≠ D.B ⊔ (K1 ⊓ K2) → IsFrobeniusWith (D.B ⊔ (K1 ⊓ K2)) (K1 ⊓ K2) D.B) →
    IsSimpleGroup G → K1 ⊓ K2 ≠ ⊥

/-! ## 8. Final arithmetic of Theorem C (pure; brute-force checked) -/

/-- **AR-C3** (p. 211, (6)+(7)+Lemma 2.5): `2k²/N ≤ (2x²+6)/(8A+1)` from (6) with
`|χᵢ(1)| ≥ 8A+1`, and `2k²/N > 1 - 3/(8A+1)` from Lemma 2.5; so `4A < x² + 4`.
`x = 0` gives `A < 1`; `x ≠ 0` gives (Frobenius, (5)) `x² ≤ 2b`, `b ≤ A`, so `b < 2`. -/
def ArithC3Prop : Prop :=
  ∀ (N k A b : ℕ) (x d1 d2 d3 dφ : ℤ), 0 < N → 1 ≤ A → 2 ≤ b →
    8 * (A : ℤ) + 1 ≤ |d1| → 8 * (A : ℤ) + 1 ≤ |d2| → 8 * (A : ℤ) + 1 ≤ |d3| →
    8 * (A : ℤ) + 1 ≤ |dφ| →
    (N : ℚ) * (1 - 3 / |(dφ : ℚ)|) < 2 * (k : ℚ) ^ 2 →
    (N : ℚ) * ((1 + x) ^ 2 / (d1 : ℚ) + (1 - x) ^ 2 / (d2 : ℚ) - 4 / (d3 : ℚ)) = 2 * (k : ℚ) ^ 2 →
    (x ≠ 0 → x ^ 2 ≤ 2 * (b : ℤ) ∧ b ≤ A) → False

/-- **AR-C4** (p. 215, "1 < 3/5 + 2/5"): if `1 + a + b + c = 0` and `Σ dᵢ = 0` with all
`|·| ≥ 5`, then `1 + 1/a + 1/b + 1/c > 3/5 > Σ 1/dᵢ`. -/
def ArithC4Prop : Prop :=
  ∀ (a b c d1 d2 d3 d4 : ℤ), 5 ≤ |a| → 5 ≤ |b| → 5 ≤ |c| → 5 ≤ |d1| → 5 ≤ |d2| →
    5 ≤ |d3| → 5 ≤ |d4| → 1 + a + b + c = 0 → d1 + d2 + d3 + d4 = 0 →
    1 + 1 / (a : ℚ) + 1 / (b : ℚ) + 1 / (c : ℚ) ≠
      1 / (d1 : ℚ) + 1 / (d2 : ℚ) + 1 / (d3 : ℚ) + 1 / (d4 : ℚ)

/-- **AR-C4b** (p. 215 top, the case of Theorem 4.3): `2k²·χ₁(1) = 8N` with `k = 2|K|`,
`(|K|, N) = 1` and `N` odd forces `|K| = 1`. -/
def ArithC4bProp : Prop :=
  ∀ (N K : ℕ) (d : ℤ), Odd N → Nat.Coprime K N →
    2 * ((2 * K : ℕ) : ℤ) ^ 2 * d = 8 * (N : ℤ) → K = 1

end Work.GW2.C16
