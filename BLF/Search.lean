import BLF.Floor

/-!
# A verified pruned search over integer vectors

`search cons bound leaf ks g` assigns, in the order `ks`, each index `k` a value `v` with `|v| ≤ bound k`,
prunes as soon as a parallelogram constraint attached to `k` fails, and evaluates `leaf` on every
complete assignment. `search_sound`: if the search returns `true`, then `leaf G = true` for every `G`
that agrees with the start vector off `ks`, respects the bounds, and satisfies the attached constraints,
provided each constraint attached to `k` only mentions `k` and indices assigned before it.
-/

namespace BLF

abbrev Quad := ℕ × ℕ × ℕ × ℕ

/-- Parallelogram constraint `|g a + g b - g c - g d| ≤ 1`. -/
def okQ (g : ℕ → ℤ) (q : Quad) : Bool := decide (|g q.1 + g q.2.1 - g q.2.2.1 - g q.2.2.2| ≤ 1)

/-- The integers `-B, ..., B`. -/
def rangeZ (B : ℕ) : List ℤ := List.map (fun t : ℕ => (t : ℤ) - (B : ℤ)) (List.range (2 * B + 1))

lemma mem_rangeZ {B : ℕ} {v : ℤ} (h : |v| ≤ B) : v ∈ rangeZ B := by
  unfold rangeZ
  rw [List.mem_map]
  refine ⟨(v + B).toNat, ?_, ?_⟩
  · rw [List.mem_range]; rw [abs_le] at h; omega
  · rw [abs_le] at h; omega

def search (cons : ℕ → List Quad) (bound : ℕ → ℕ) (leaf : (ℕ → ℤ) → Bool) :
    List ℕ → (ℕ → ℤ) → Bool
  | [], g => leaf g
  | k :: ks, g => (rangeZ (bound k)).all fun v =>
      !((cons k).all (okQ (Function.update g k v))) ||
        search cons bound leaf ks (Function.update g k v)

/-- Every constraint attached to `k` mentions only indices not assigned after `k`. -/
def wfB (cons : ℕ → List Quad) : List ℕ → Bool
  | [] => true
  | k :: ks => (cons k).all (fun q => !(ks.contains q.1) && !(ks.contains q.2.1) &&
      !(ks.contains q.2.2.1) && !(ks.contains q.2.2.2)) && wfB cons ks

lemma okQ_congr (g G : ℕ → ℤ) (q : Quad) (h1 : g q.1 = G q.1) (h2 : g q.2.1 = G q.2.1)
    (h3 : g q.2.2.1 = G q.2.2.1) (h4 : g q.2.2.2 = G q.2.2.2) : okQ g q = okQ G q := by
  unfold okQ; rw [h1, h2, h3, h4]

theorem search_sound (cons : ℕ → List Quad) (bound : ℕ → ℕ) (leaf : (ℕ → ℤ) → Bool) :
    ∀ (ks : List ℕ) (g G : ℕ → ℤ), search cons bound leaf ks g = true → wfB cons ks = true →
      (∀ m, m ∉ ks → g m = G m) → (∀ k ∈ ks, |G k| ≤ bound k) →
      (∀ k ∈ ks, (cons k).all (okQ G) = true) → leaf G = true := by
  intro ks
  induction ks with
  | nil =>
    intro g G hs _ hg _ _
    have : g = G := funext fun m => hg m (by simp)
    subst this; simpa [search] using hs
  | cons k ks ih =>
    intro g G hs hwf hg hb hc
    simp only [wfB, Bool.and_eq_true, List.all_eq_true] at hwf
    obtain ⟨hwq, hwf⟩ := hwf
    set g' := Function.update g k (G k) with hg'
    have agree : ∀ m, m ∉ ks → g' m = G m := by
      intro m hm
      by_cases hmk : m = k
      · subst hmk; simp [hg']
      · rw [hg', Function.update_of_ne hmk]; exact hg m (by simp [hmk, hm])
    have hv := hb k (by simp)
    simp only [search, List.all_eq_true] at hs
    have hk := hs (G k) (mem_rangeZ hv)
    have hcons : (cons k).all (okQ g') = true := by
      rw [List.all_eq_true]
      intro q hq
      have hqk := hc k (by simp)
      rw [List.all_eq_true] at hqk
      have w := hwq q hq
      simp at w
      obtain ⟨⟨⟨w1, w2⟩, w3⟩, w4⟩ := w
      rw [okQ_congr g' G q (agree _ w1) (agree _ w2) (agree _ w3) (agree _ w4)]
      exact hqk q hq
    rw [hcons] at hk
    simp only [Bool.not_true, Bool.false_or] at hk
    exact ih g' G hk hwf agree (fun k' hk' => hb k' (by simp [hk']))
      (fun k' hk' => hc k' (by simp [hk']))

end BLF
