
def get (as : List Nat) (i : Nat) : Option Nat := by
  match as with
  | .nil => exact none
  | .cons a bs =>
    match i with
    | 0 => exact some a
    | i + 1 => exact get bs i


theorem get_none (as : List Nat) (i : Nat) (h : get as i = none) : i ≥ as.length := by
  revert i
  induction as with
  | nil => simp
  | cons b bs ih =>
    intro i
    induction i with
    | zero => simp [_root_.get]
    | succ i ihi => simp [_root_.get, List.length]; apply ih

theorem get_some (as : List Nat) (i c : Nat)(h : get as i = some c) : i < as.length := by
  revert i
  induction as with
  | nil => intros; simp_all[_root_.get]
  | cons b bs ih =>
    intro i
    induction i with
    | zero => simp [_root_.get]
    | succ i ihi => simp [_root_.get, List.length]; apply ih





--#eval (get [6, 4, 1, 0, 44, 8] 4)


def search (a : Nat) (as : List Nat) : Bool := by
  match as with
  | .nil => exact false
  | .cons b bs => match Nat.decEq a b with
                  | isTrue _ => exact true
                  | isFalse _ => exact (search a bs)



-- #eval (search 1 [6, 4, 1, 0, 8])


def search_interval (a : Nat) (as : List Nat) (l m : Nat) : Bool := by
  match as with
  | .nil => exact false
  | .cons b bs =>
    match l, m with
    | _, 0 => exact false
    | l + 1, m + 1 => exact search_interval a bs l (m + 1)
    | 0, m + 1 => match Nat.decEq a b with
              | isTrue _ => exact true
              | isFalse _ => exact (search_interval a bs 0 m)

-- #eval (search_interval 77 [1, 3, 6, 9, 11, 17, 22, 34, 56, 77] 0 100)

theorem search_interval_correct (a : Nat) (as : List Nat) :
  search a as = search_interval a as 0 as.length := by
  induction as with
  | nil => rfl
  | cons b bs ih => simp [search, search_interval, ih]


theorem search_interval_split (a : Nat) (as : List Nat) (l m t : Nat) :
  search_interval a as l (m + t) =
  or (search_interval a as l m) (search_interval a as (l + m) t) := by
  revert m l t
  induction as with
  | nil => intros; rfl
  | cons b bs ih =>
    intro l m t
    match m, t with
    | 0, 0 => rfl
    | 0, t + 1 => have : (0 + (t + 1)) = (t + 1) := by apply Nat.zero_add
                  rw [this]; rfl
    | m + 1, 0 => have : search_interval a (b :: bs) (l + (m + 1)) 0 = false := by rfl
                  rw [this, Bool.or_false];
    | m + 1, t + 1 =>
      induction l with
      | zero => match Nat.decEq a b with
                | isTrue heq =>
                  have h₁ : (search_interval a (b :: bs) 0 ((m + 1) + (t + 1)) = true) := by
                    simp [search_interval]
                    split
                    . rfl
                    . simp_all
                  have h₂ : (search_interval a (b :: bs) 0 ((m + 1)) = true) := by
                    simp [search_interval]
                    split
                    . rfl
                    . simp_all
                  rw [h₁, h₂]; rw [Bool.true_or]
                | isFalse hneq =>
                  have h₁ : (search_interval a (b :: bs) 0 ((m + 1) + (t + 1)) =
                              search_interval a (bs) 0 ((m + 1) + t)) := by
                              simp [search_interval]
                              split
                              . simp_all
                              . rfl
                  have h₂ : (search_interval a (b :: bs) (0 + (m + 1)) (t + 1) =
                              search_interval a (bs) (0 + m) (t + 1)) := by
                              --have : 0 + (m + 1) = m + 1 := by apply Nat.zero_add
                              simp [search_interval]
                  have h₃ : (search_interval a (b :: bs) 0 ((m + 1)) =
                              search_interval a (bs) 0 m) := by
                              simp [search_interval]
                              split
                              . simp_all
                              . rfl
                  simp only [h₁, h₃, h₂]
                  have : m + 1 + t = m + (t + 1) := by omega
                  rw [this]; apply ih
      | succ l => simp only [search_interval];
                  have : (l + 1).add m = (l + 1) + m := by rfl;
                  rw [this]
                  have : (m + 1).add t + 1 = (m + 1) + (t + 1) := by rfl;
                  rw [this]
                  have : (l + 1) + m = l + (m + 1) := by omega;
                  rw [this]
                  apply ih




def bin_search_interval (a : Nat) (as : List Nat) (l m : Nat) : Bool := by
  match m with
  | 0 => exact false
  | 1 => let b := get as l
         match b with
         | none => exact false
         | some c => match (Nat.decEq a c) with
                     | isTrue _ => exact true
                     | isFalse _ => exact false
  | n + 2 => let m := n + 2
             let t := (m / 2)
             let b := get as (l + t)
             match b with
             | none => exact (bin_search_interval a as l t)
             | some c => match Nat.decLt a c with
                         | isTrue _ => exact (bin_search_interval a as l t)
                         | isFalse _ => exact (bin_search_interval a as (l + t) (m - t))


-- #eval (bin_search_interval 77 [1, 3, 6, 9, 11, 17, 22, 34, 56, 77] 7 100)


theorem trivial_search_interval_true (a : Nat) (as : List Nat) (l m : Nat) (h : some a = get as l):
  search_interval a as l (m + 1) = true := by
  revert as
  induction l with
  | zero => intro as h
            match as with
            | .nil => simp_all [_root_.get]
            | .cons b bs => simp_all [_root_.get, search_interval]
                            split
                            . rfl
                            . simp_all
  | succ l ih => intro as h
                 match as with
                 | .nil => simp_all [_root_.get]
                 | .cons b bs => simp_all [_root_.get, search_interval]


theorem trivial_search_interval_false (a : Nat) (as : List Nat) (l : Nat)
                                      (c : Nat) (h₁ : ¬c = a) (h₂ : some c = get as l):
  search_interval a as l 1 = false := by
  revert as
  induction l with
  | zero => intro as h
            match as with
            | .nil => simp_all [_root_.get]
            | .cons b bs => simp_all [_root_.get, search_interval]
                            split
                            . simp_all
                            . match bs with
                              | .nil => rfl
                              | .cons c cs => rfl
  | succ l ih => intro as h
                 match as with
                 | .nil => simp_all [_root_.get]
                 | .cons b bs => simp_all [_root_.get, search_interval]

theorem search_interval_big_l (a : Nat) (as : List Nat) (l m : Nat) (h : l ≥ as.length) :
  search_interval a as l m = false := by
  revert l
  induction as with
  | nil => intros; rfl
  | cons b bs ih =>
    intro l h
    match l with
    | 0 => simp_all
    | l + 1 => match m with
      | 0 => rfl
      | m + 1 => simp [search_interval]; apply ih; simp at h; assumption

def sorted : (as : List Nat) → Prop
  | [] => True
  | [_] => True
  | a :: b :: bs => (a ≤ b) ∧ (sorted (b :: bs))

example : sorted [1, 2, 5, 6] := by simp [sorted]

theorem tail_is_sorted (a : Nat) (as : List Nat) (h : sorted (a :: as)) : sorted as := by
  match as with
  | [] => trivial
  | [b] => trivial
  | b :: c :: bs => have ⟨h_le, h_tail_sorted⟩ := h; assumption


theorem search_small_a (a : Nat) (as : List Nat) (l m : Nat) (h_sorted : sorted as)
    (c : Nat) (h_get : get as l = some c) (h_lt : a < c) : search_interval a as l m = false := by
    revert l
    match as with
    | [] => intros; rfl
    | b :: bs => intro l h_get
                 match l with
                 | 0 => match m with
                        | 0 => rfl
                        | m + 1 => simp [search_interval]
                                   split
                                   . simp [_root_.get] at h_get; simp_all
                                   . simp [_root_.get] at h_get
                                     have h_sorted_bs := tail_is_sorted b bs h_sorted
                                     let d := get bs 0
                                     have h_d_eq_get : d = get bs 0 := by rfl
                                     match d with
                                     | none => have : bs.length = 0 := by
                                                    apply Nat.le_zero.mp; apply get_none; simp_all
                                               have : bs = [] := by
                                                    apply List.length_eq_zero_iff.mp; assumption
                                               rw [this]; rfl
                                     | some d' => match bs with
                                                  | [] => rfl
                                                  | d'' :: cs =>
                                                    have h_eq_d: d' = d'' := by
                                                      simp [_root_.get] at h_d_eq_get; assumption
                                                    have h_b_le_d: b ≤ d'' := by exact h_sorted.1
                                                    have h_a_lt_d'': a < d'' := by omega
                                                    have h_get_new : get (d'' :: cs) 0 = some d'' := by
                                                      rw [← h_eq_d]; rfl
                                                    exact search_small_a a (d'' :: cs) 0 m h_sorted_bs d'' h_get_new h_a_lt_d''
                 | l + 1 => match m with
                            | 0 => rfl
                            | m + 1 =>
                              simp [search_interval]
                              have h_sorted_bs := tail_is_sorted b bs h_sorted
                              match bs with
                              | [] => rfl
                              | d :: cs =>
                                have h_get_new : _root_.get (d :: cs) l = some c := by simp_all [_root_.get]
                                exact search_small_a a (d :: cs) l (m + 1) h_sorted_bs c h_get_new h_lt


theorem sorted_list_elems (as : List Nat) (h_sorted : sorted as) (i j a b: Nat) (h_le : i ≤ j)
  (h₁ : get as i = some a) (h₂ : get as j = some b) : a ≤ b := by
  match as with
  | [] => simp [_root_.get] at h₁
  | c :: bs =>
    match i, j with
    | 0, 0 => simp [_root_.get] at h₁ h₂; rw [← h₁, h₂]; apply Nat.le_refl
    | i + 1, 0 => simp_all
    | 0, j + 1 => simp [_root_.get] at h₁ h₂
                  match bs with
                  | [] => simp [_root_.get] at h₂
                  | d :: cs => have h_a_le_d : a ≤ d := by rw [←h₁]; exact h_sorted.1
                               have h1_new : get (d :: cs) 0 = some d := by rfl
                               have d_d_le_b : d ≤ b := by
                                 exact sorted_list_elems (d :: cs) h_sorted.2 0 j d b (Nat.zero_le j) h1_new h₂
                               exact Nat.le_trans h_a_le_d d_d_le_b
    | i + 1, j + 1 => simp_all [_root_.get]
                      have : sorted bs := by apply tail_is_sorted c bs h_sorted
                      apply sorted_list_elems bs this i j a b h_le h₁ h₂

theorem sorted_list_elems_contra (as : List Nat) (h_sorted : sorted as) (i j a b: Nat) (h_lt: a < b)
  (h₁ : get as i = some a) (h₂ : get as j = some b) : i < j := by
  by_cases h : i < j
  . assumption
  . have h_le : j ≤ i := by omega
    have h_bad : b ≤ a := by exact sorted_list_elems as h_sorted j i b a h_le h₂ h₁
    omega


theorem search_big_a (a : Nat) (as : List Nat) (l m : Nat) (h_sorted : sorted as)
    (c : Nat) (h_get : get as (l + m) = some c) (h_lt : a > c) : search_interval a as l m = false := by
    revert l
    match as with
    | [] => intros; rfl
    | b :: bs =>
      intro l h_get
      have h_sorted_bs : sorted bs := tail_is_sorted b bs h_sorted
      match l with
      | 0 =>
        match m with
        | 0 => rfl
        | m + 1 =>
          have h_get_0: get (b :: bs) 0 = b := by rfl
          have : 0 + (m + 1) = m + 1 := by apply Nat.zero_add
          rw [this] at h_get
          have : 0 ≤ m + 1 := by apply Nat.zero_le
          have h_b_le_c : b ≤ c := by
            exact sorted_list_elems (b :: bs) h_sorted 0 (m + 1) b c this h_get_0 h_get
          simp [search_interval]
          split
          . simp_all
            have : ¬ b ≤ c := by omega
            simp_all
          . --have h_sorted_bs : sorted bs := tail_is_sorted b bs h_sorted
            simp [_root_.get] at h_get
            rw [← Nat.zero_add m] at h_get
            exact search_big_a a bs 0 m h_sorted_bs c h_get h_lt
      | l + 1 => match m with
        | 0 => rfl
        | m + 1 =>
          simp [search_interval]
          simp [_root_.get] at h_get
          have : l + (m + 1) = l + 1 + m := by omega
          rw [← this] at h_get
          exact search_big_a a bs l (m + 1) h_sorted_bs c h_get h_lt


theorem bin_search_of_a_member (a : Nat) (as : List Nat) (l m i : Nat) (h_le : l ≤ i) (h_lt : i < l + m)
  (h_get : get as i = a) (h_sorted : sorted as) : bin_search_interval a as l m = true := by
  match m with
  | 0 => omega
  | 1 =>
    have h_eq : i = l := by omega
    simp only [bin_search_interval]
    split
    . rw [h_eq] at h_get
      simp_all
    . split
      . rfl
      . rw [h_eq] at h_get
        simp_all
        symm at h_get
        simp_all
  | n + 2 =>
    let m := n + 2
    let t := m / 2
    let r := m - t
    let b := get as (l + t)
    have h_b : get as (l + t) = b := by rfl
    match b with
    | none =>
      have h_small_len : l + t ≥ as.length := by apply get_none; assumption
      have h_small_i : i < as.length := by apply get_some as i a h_get
      have h_lt_new : i < l + t := by omega
      simp only [bin_search_interval]
      split
      . exact bin_search_of_a_member a as l t i h_le h_lt_new h_get h_sorted
      . split; all_goals
        have : l + t = (l + (n + 2) / 2) := by rfl
        rw [this] at h_b; simp_all
    | some c =>
      simp only [bin_search_interval]
      split
      . have : l + t = (l + (n + 2) / 2) := by rfl
        rw [this] at h_b; simp_all
      . split
        . have : l + t = (l + (n + 2) / 2) := by rfl
          rw [this] at h_b;
          have h_a_lt_c : a < c := by simp_all
          have h_lt_new : i < l + t := by exact sorted_list_elems_contra as h_sorted i (l + t) a c h_a_lt_c h_get h_b
          exact bin_search_of_a_member a as l t i h_le h_lt_new h_get h_sorted
        . have : t = (n + 2)/2 := by rfl
          rw [this] at h_b;
          have h_c_le_a : c ≤ a := by cases Nat.lt_or_ge a c
                                      case inl h => simp_all
                                      case inr h => assumption
          cases Nat.le_iff_lt_or_eq.mp h_c_le_a
          case inl h =>
            have h_le_new : l + t ≤ i := by
              have : l + t < i → l + t ≤ i := by omega
              apply this
              apply sorted_list_elems_contra as h_sorted (l + t) i c a h h_b h_get
            have h_lt_new : i < (l + t) + r := by omega
            exact bin_search_of_a_member a as (l + t) r i h_le_new h_lt_new h_get h_sorted
          case inr h =>
            have h_get_new : get as (l + (n + 2) / 2) = some a := by rw [← h]; assumption
            have h_le_new : l + t ≤ l + t := by apply Nat.le_refl
            have h_lt_new : l + t < l + t + r := by omega
            exact bin_search_of_a_member a as (l + t) r (l + t) h_le_new h_lt_new h_get_new h_sorted





theorem bin_search_interval_correct (a : Nat) (as : List Nat) (l m : Nat) (h_sorted : sorted as) :
  bin_search_interval a as l m = search_interval a as l m := by
  match m with
  | 0 => match as with
         | .nil => simp [search_interval, bin_search_interval]
         | .cons b bs => simp [search_interval, bin_search_interval]
  | 1 => let b := get as l
         have h_get : b = get as l := by rfl
         match b with
         | none =>
           have : l ≥ as.length := by apply get_none; symm; assumption
           have : search_interval a as l 1 = false := by apply search_interval_big_l; assumption
           rw [this]
           simp [bin_search_interval]
           split
           . rfl
           . split
             . simp_all
             . rfl
         | some c =>
           match Nat.decEq a c with
           | isTrue heq => simp [bin_search_interval]
                           have h_some_eq : some a = get as l := by rw [heq]; exact h_get
                           rw [trivial_search_interval_true a as l 0 h_some_eq]
                           split
                           . simp_all
                           . split
                             . rfl
                             . simp_all
           | isFalse hneq => simp [bin_search_interval]
                             have h_some_neq : ¬some a = get as l := by rw [← h_get];
                                                                        intro h
                                                                        have : a = c := Option.some_inj.mp h
                                                                        simp_all
                             split
                             . have : l ≥ as.length := by apply get_none; assumption
                               symm; apply search_interval_big_l; assumption
                             . split
                               . simp_all
                               . symm; apply trivial_search_interval_false a as l c
                                 . intro h_eq; symm at h_eq; exact hneq h_eq
                                 . assumption
    | n + 2 => let m := n + 2
               let t := (m / 2)
               let r := m - t
               let b := get as (l + t)
               have h_get : get as (l + t) = b := by rfl
               match b with
               | none =>
                 have : t + r = n + 2 := by omega
                 rw [← this]
                 rw [search_interval_split a as l t r]
                 rw [this]
                 simp only [bin_search_interval]
                 have h_small_len : (l + t) ≥ as.length := by apply get_none; assumption
                 have : search_interval a as (l + t) r = false := by
                   apply search_interval_big_l ; assumption
                 rw [this]; rw [Bool.or_false]
                 split
                 . exact bin_search_interval_correct a as l t h_sorted
                 . split; all_goals
                   have : t = (n + 2) / 2 := by rfl
                   rw [this] at h_get
                   simp_all
               | some c =>
                 have h_lt_or_ge := Nat.lt_or_ge a c
                 have h_or : a < c ∨ a = c ∨ a > c := by omega
                 cases h_or
                 case inl h =>
                   have : t + r = n + 2 := by omega
                   rw [← this]
                   rw [search_interval_split a as l t r]
                   rw [this]
                   simp only [bin_search_interval]
                   have : search_interval a as (l + t) r = false :=
                     by apply search_small_a a as (l + t) r h_sorted c h_get h
                   rw [this]; rw [Bool.or_false]
                   split
                   . have : l + t = l + (n + 2) / 2 := by rfl
                     rw [this] at h_get
                     simp_all
                   . split
                     . have : (n + 2) / 2 = t := by rfl
                       rw [this]
                       exact bin_search_interval_correct a as l t h_sorted
                     . have : (n + 2) / 2 = t := by rfl
                       rw [this]
                       simp_all
                 case inr h_ge =>
                   cases h_ge
                   case inr h =>
                     have : t + r = n + 2 := by omega
                     rw [← this]
                     rw [search_interval_split a as l t r]
                     rw [this]
                     simp only [bin_search_interval]
                     have : search_interval a as l t = false :=
                       by apply search_big_a a as l t h_sorted c h_get h
                     rw [this]; rw [Bool.false_or]
                     split
                     . have : l + t = l + (n + 2) / 2 := by rfl
                       rw [this] at h_get
                       simp_all
                     . split
                       . have : l + t = l + (n + 2) / 2 := by rfl
                         rw [this] at h_get
                         simp_all
                         omega
                       . have : l + (n + 2) / 2 = l + t := by omega
                         rw [this]
                         have : n + 2 - (n + 2) / 2 = r := by rfl
                         rw [this]
                         exact bin_search_interval_correct a as (l + t) r h_sorted
                   case inl h =>
                     have h_get_symm : some a = get as (l + t) := by symm; rw [h]; assumption
                     have h_r_pos : (r - 1) + 1 = r := by omega
                     have h_search_true : search_interval a as (l + t) r = true := by
                       rw [← h_r_pos]
                       exact trivial_search_interval_true a as (l + t) (r - 1) h_get_symm
                     have : n + 2 = t + r := by omega
                     rw [this]
                     have : search_interval a as l (t + r) = true := by
                       rw [search_interval_split a as l t r]
                       rw [h_search_true]
                       apply Bool.or_true
                     rw [this]
                     apply bin_search_of_a_member a as l (t + r) (l + t) (by omega) (by omega) (by simp_all) h_sorted


def bin_search (a : Nat) (as : List Nat) : Bool := bin_search_interval a as 0 as.length

theorem bin_search_correct (a : Nat) (as : List Nat) (h_sorted : sorted as):
  bin_search a as = search a as := by
  simp only [bin_search]
  rw [search_interval_correct]
  apply bin_search_interval_correct
  assumption


theorem search_spec (a : Nat) (as : List Nat) :
  search a as = true ↔ ∃ i, _root_.get as i = some a := by
  constructor
  . induction as with
    | nil => simp only [search]; simp_all
    | cons b bs ih =>
      unfold search
      match Nat.decEq a b with
      | isTrue h_eq =>
        intros
        exists 0
        rw [h_eq]
        rfl
      | isFalse h_neq =>
        intro h
        simp only at h
        let ⟨i, h_get⟩ := ih h
        exists i + 1
  . intro h
    let ⟨i, h_get⟩ := h
    rw [search_interval_correct]
    let m := as.length - 1 - i
    have : as.length > i := by apply get_some as i a h_get
    have : as.length = i + (m + 1) := by omega
    rw [this]
    rw [search_interval_split]
    have : search_interval a as (0 + i) (m + 1) = true := by
      apply trivial_search_interval_true
      rw [Nat.zero_add, h_get]
    rw [this]
    exact Bool.or_true (search_interval a as 0 i)




theorem bin_search_spec (a : Nat) (as : List Nat) (h_sorted : sorted as) :
  bin_search a as = true ↔ ∃ i, _root_.get as i = some a := by
  rw [bin_search_correct]
  . apply search_spec
  . assumption
